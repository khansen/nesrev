import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * NESrev - A disassembler for NES PRG-ROMs
 *
 * @author Kent Hansen
 **/

public class NESrev {

    // status bit defs (OR masks)
    private static int CODE = 0x01, DATA = 0x02, LABEL = 0x04, PTR = 0x08, INSTR = 0x10;
    // corresponding AND masks
    private static int NOT_CODE = 0xFE, NOT_DATA = 0xFD, NOT_LABEL = 0xFB, NOT_PTR = 0xF7, NOT_INSTR = 0xEF;
    // enumerated NES addressing modes
    private static int UNDF=0, IMPL=1, IMMD=2, ZERO=3, ZERX=4, ZERY=5, ABSL=6, ABSX=7, ABSY=8, INDR=9, INDX=10, INDY=11, RELV=12;
    // the ROM contents
    private static int[] ROM;
    private static final int MAPPER_NROM = 0;
    private static final int MAPPER_MMC1 = 1;
    // PRG mapping. NROM-128 uses a 16 KB PRG mirrored at $C000; NROM-256
    // uses a 32 KB PRG mapped contiguously at $8000. MMC1 support treats
    // each 16 KB bank as a distinct address space: banks before the final
    // fixed bank live in the $8000-$BFFF window, and the final bank lives in
    // the $C000-$FFFF window.
    private static int mapperNumber = MAPPER_NROM;
    private static int prgSize = 0x4000;
    private static int prgMask = 0x3FFF;
    private static int cpuBase = 0xC000;
    private static int fixedBankOffset = 0x0000;
    // the status map
    private static int[] map;
    // the name of the ROM, extracted from the cmdline arg
    private static String name;
    // is set to true if HTML output is desired
    private static boolean toHtml=false;
    // iterative code target worklist used by processCode()
    private static ArrayDeque<Integer> codeWorklist = new ArrayDeque<Integer>();
    private static boolean processCodeActive = false;
    // Per-byte hard "do not decode as code" mask. Distinct from the existing
    // DATA bit, which also means "unclassified and eligible for tracing." Set
    // for: configured data-range bytes and resolved inline-record bytes.
    // processCodeSingle must stop before decoding a byte where this is true.
    private static boolean[] blockedFromCode = new boolean[0x4000];
    // Parsed configuration. Defaulted to EMPTY until main() loads them or a
    // test sets them via reflection.
    private static InlineCallsConfig inlineCalls = InlineCallsConfig.EMPTY;
    private static DataRangesConfig dataRanges = DataRangesConfig.EMPTY;
    // Lifted from main() local scope so runAnalysisPass() can re-apply seeds
    // on each restart pass.
    private static ArrayList<Integer> codePointersStart = new ArrayList<Integer>();
    private static ArrayList<Integer> codePointersCount = new ArrayList<Integer>();
    private static ArrayList<Integer> dataPointersStart = new ArrayList<Integer>();
    private static ArrayList<Integer> dataPointersCount = new ArrayList<Integer>();
    private static ArrayList<Integer> codeEntries = new ArrayList<Integer>();
    private static int userCodePointersCount = 0;
    // Resolved inline records known so far, keyed by callsite PRG offset.
    // TreeMap so iteration is in callsite order each pass — keeps trace
    // results independent of the order callsites were discovered.
    private static TreeMap<Integer, ResolvedRecord> knownCallsites = new TreeMap<Integer, ResolvedRecord>();
    // Callsites discovered during the current pass that aren't yet in
    // knownCallsites. The restart loop promotes them at end-of-pass.
    private static LinkedHashSet<Integer> newlyDiscoveredCallsites = new LinkedHashSet<Integer>();
    // Safety cap for the fixed-point inline-call analysis. Tests lower this
    // through reflection to verify the failure path without building a huge ROM.
    private static int analysisPassLimit = 0x4000;
    // Output-time indices built at the start of disassemble() from
    // knownCallsites and dataRanges. recordsByStart dispatches inline-record
    // emission; dataBoundaries breaks .DB runs at record/range edges.
    private static HashMap<Integer, ResolvedRecord> recordsByStart = new HashMap<Integer, ResolvedRecord>();
    private static TreeSet<Integer> dataBoundaries = new TreeSet<Integer>();
    // table-driven opcode classifications used by processCodeSingle()
    private static final boolean[] RELATIVE_BRANCH_OPCODE = createOpcodeFlagTable(
        0x10, 0x30, 0x50, 0x70, 0x90, 0xB0, 0xD0, 0xF0
    );
    private static final boolean[] CHECK_DATA_LABEL_OPCODE = createOpcodeFlagTable(
        0x0D, 0x0E, 0x19, 0x1D, 0x1E,
        0x2C, 0x2D, 0x2E, 0x39, 0x3D, 0x3E,
        0x4D, 0x4E, 0x59, 0x5D, 0x5E,
        0x6D, 0x6E, 0x79, 0x7D, 0x7E,
        0xAC, 0xAD, 0xAE, 0xB9, 0xBC, 0xBD, 0xBE,
        0xCC, 0xCD, 0xD9, 0xDD, 0xEC, 0xED, 0xF9, 0xFD
    );

    private static void printUsage() {
        System.out.println("Syntax: java NESrev [ROMfile] <-mapper 0|1|nrom|mmc1> <-html> <-codepointers FILE> <-datapointers FILE> <-codeentries FILE> <-inlinecalls FILE> <-dataranges FILE>");
    }

    private static void exitWithError(String message) {
        System.err.println(message);
        System.exit(1);
    }

    private static int parseMapperNumber(String token) {
        String value = token.trim().toLowerCase();
        if (value.equals("0") || value.equals("nrom")) {
            return MAPPER_NROM;
        }
        if (value.equals("1") || value.equals("mmc1")) {
            return MAPPER_MMC1;
        }
        exitWithError("Error: Unsupported mapper '" + token + "'. Supported mappers: 0 (NROM), 1 (MMC1).");
        return MAPPER_NROM;
    }

    private static int parseMapperOption(String[] args) {
        int mapper = MAPPER_NROM;
        for (int i = 1; i < args.length; i++) {
            if (!args[i].equals("-mapper")) {
                continue;
            }
            if (i + 1 >= args.length) {
                exitWithError("Error: Missing mapper number after -mapper.");
            }
            mapper = parseMapperNumber(args[i + 1]);
            i++;
        }
        return mapper;
    }

    private static void parsePointerTableConfig(String path, String kindLabel,
                                                ArrayList<Integer> startsOut,
                                                ArrayList<Integer> countsOut) throws Exception {
        File configFile = new File(path);
        if (!configFile.canRead()) {
            exitWithError("Error: Couldn't read " + path + ".");
        }
        try (BufferedReader br = new BufferedReader(new FileReader(configFile))) {
            String line;
            int lineNo = 0;
            while ((line = br.readLine()) != null) {
                lineNo++;
                line = stripConfigComments(line).trim();
                if (line.length() == 0) {
                    continue;
                }
                if (line.equalsIgnoreCase("start|count") || line.equalsIgnoreCase("bank|addr|count")) {
                    continue;
                }
                String[] parts = line.split("\\|", -1);
                if (parts.length != 2 && parts.length != 3) {
                    exitWithError("Error: Bad " + kindLabel + " config format at line " + lineNo + ": " + line);
                }
                int offset;
                int count;
                try {
                    if (parts.length == 2) {
                        offset = Integer.decode(parts[0].trim());
                        count = Integer.decode(parts[1].trim());
                    } else {
                        offset = parseBankedPrgOffset(kindLabel, parts[0].trim(), parts[1].trim(), lineNo);
                        count = Integer.decode(parts[2].trim());
                    }
                } catch (NumberFormatException ex) {
                    exitWithError("Error: Bad numeric value at line " + lineNo + ": " + line);
                    return;
                } catch (ConfigException ex) {
                    exitWithError("Error: " + ex.getMessage());
                    return;
                }
                long pointerTableEnd = (long) offset + ((long) count * 2L);
                if (offset < 0 || count < 0 || pointerTableEnd > (long) prgSize) {
                    exitWithError("Error: " + kindLabel + " addresses are out of range at line " + lineNo + ".");
                }
                startsOut.add(offset);
                countsOut.add(count);
            }
        }
    }

    private static int parseBankedPrgOffset(String kindLabel, String bankStr, String cpuStr, int lineNo) {
        int bank;
        int cpu;
        try {
            bank = Integer.decode(bankStr);
            cpu = parseRawCpuAddress(kindLabel, cpuStr, lineNo);
        } catch (NumberFormatException ex) {
            throw new ConfigException(kindLabel + ": bad bank value at line " + lineNo + ": " + bankStr);
        }
        return bankedCpuToPrgOffset(kindLabel, bank, cpu, lineNo);
    }

    private static int bankedCpuToPrgOffset(String kindLabel, int bank, int cpu, int lineNo) {
        if (mapperNumber != MAPPER_MMC1) {
            throw new ConfigException(kindLabel + ": bank-qualified rows require mapper 1 (MMC1)");
        }
        int bankCount = prgSize / 0x4000;
        if (bank < 0 || bank >= bankCount) {
            throw new ConfigException(kindLabel + ": bank " + bank
                + " is outside available banks 0.." + (bankCount - 1)
                + " at line " + lineNo);
        }
        if (bank == bankCount - 1) {
            if (cpu < 0xC000 || cpu > 0xFFFF) {
                throw new ConfigException(kindLabel + ": fixed final bank " + bank
                    + " requires a $C000-$FFFF address at line " + lineNo
                    + ": $" + hex4(cpu));
            }
            return (bank * 0x4000) + (cpu - 0xC000);
        }
        if (cpu < 0x8000 || cpu > 0xBFFF) {
            throw new ConfigException(kindLabel + ": switchable bank " + bank
                + " requires a $8000-$BFFF address at line " + lineNo
                + ": $" + hex4(cpu));
        }
        return (bank * 0x4000) + (cpu - 0x8000);
    }

    private static boolean[] createOpcodeFlagTable(int... opcodes) {
        boolean[] flags = new boolean[256];
        for (int op : opcodes) {
            flags[op & 0xFF] = true;
        }
        return flags;
    }

    private static boolean[] createProcessableOpcodeTable() {
        boolean[] flags = new boolean[256];
        for (int op = 0; op < 256; op++) {
            if ((op != 0x00) && !mnemonicLookup[op].equals("???")) {
                flags[op] = true;
            }
        }
        return flags;
    }

    private static void configurePrgMapping(long length) {
        configurePrgMapping(length, MAPPER_NROM);
    }

    private static void configurePrgMapping(long length, int mapper) {
        mapperNumber = mapper;
        if (mapper == MAPPER_NROM && length == 0x4000L) {
            prgSize = 0x4000;
            prgMask = 0x3FFF;
            cpuBase = 0xC000;
            fixedBankOffset = 0x0000;
        } else if (mapper == MAPPER_NROM && length == 0x8000L) {
            prgSize = 0x8000;
            prgMask = 0x7FFF;
            cpuBase = 0x8000;
            fixedBankOffset = 0x0000;
        } else if (mapper == MAPPER_MMC1) {
            if (length < 0x4000L || (length % 0x4000L) != 0 || length > 0x40000L) {
                exitWithError("Error: MMC1 PRG ROM must be 16 KB aligned and no larger than 256 KB.");
            }
            prgSize = (int) length;
            prgMask = 0x3FFF;
            cpuBase = 0xC000;
            fixedBankOffset = prgSize - 0x4000;
        } else {
            exitWithError("Error: NROM PRG ROM must be 16,384 or 32,768 bytes in size.");
        }
        analysisPassLimit = prgSize;
    }

    private static boolean inPrgOffset(int ofs) {
        return ofs >= 0 && ofs < prgSize;
    }

    private static boolean isTraceablePrgOffset(int ofs) {
        return inPrgOffset(ofs);
    }

    private static int normalizePrgOffset(int ofs) {
        if (mapperNumber == MAPPER_MMC1) {
            return ofs >= 0 && ofs < prgSize ? ofs : -1;
        }
        return ofs & prgMask;
    }

    private static int offsetToCpu(int ofs) {
        if (mapperNumber == MAPPER_MMC1) {
            int bankOffset = ofs & 0x3FFF;
            if (ofs >= fixedBankOffset) {
                return 0xC000 + bankOffset;
            }
            return 0x8000 + bankOffset;
        }
        return cpuBase + ofs;
    }

    private static int cpuToPrgOffset(int cpu) {
        if (mapperNumber == MAPPER_MMC1) {
            return cpuToPrgOffsetForContext(cpu, fixedBankOffset);
        }
        if (!isCpuRomAddress(cpu)) {
            throw new ConfigException("CPU address $" + hex4(cpu)
                + " is outside CPU ROM space $8000-$FFFF");
        }
        if (prgSize == 0x4000) {
            return cpu & 0x3FFF;
        }
        return cpu - cpuBase;
    }

    private static int cpuToPrgOffsetForContext(int cpu, int contextOfs) {
        if (!isCpuRomAddress(cpu)) {
            throw new ConfigException("CPU address $" + hex4(cpu)
                + " is outside CPU ROM space $8000-$FFFF");
        }
        if (mapperNumber == MAPPER_MMC1) {
            if (!inPrgOffset(contextOfs)) {
                throw new ConfigException("MMC1 context offset $" + hex4(contextOfs)
                    + " is outside PRG ROM");
            }
            if (cpu >= 0xC000) {
                return fixedBankOffset + (cpu - 0xC000);
            }
            if (contextOfs >= fixedBankOffset) {
                throw new ConfigException("CPU address $" + hex4(cpu)
                    + " is in the MMC1 switchable PRG window $8000-$BFFF without a bank context");
            }
            return bankBaseOffset(contextOfs) + (cpu - 0x8000);
        }
        return cpuToPrgOffset(cpu);
    }

    private static int bankBaseOffset(int ofs) {
        return ofs & ~0x3FFF;
    }

    private static int bankNumberForOffset(int ofs) {
        return ofs / 0x4000;
    }

    private static boolean isCpuRomAddress(int cpu) {
        return cpu >= 0x8000 && cpu <= 0xFFFF;
    }

    private static boolean isStaticallyMappedCpuAddress(int cpu, int contextOfs) {
        if (!isCpuRomAddress(cpu)) {
            return false;
        }
        return mapperNumber != MAPPER_MMC1
            || cpu >= 0xC000
            || (inPrgOffset(contextOfs) && contextOfs < fixedBankOffset);
    }

    private static boolean isCanonicalCpuAddress(int cpu) {
        if (mapperNumber == MAPPER_MMC1) {
            return cpu >= 0xC000 && cpu <= 0xFFFF;
        }
        return cpu >= cpuBase && cpu <= 0xFFFF;
    }

    private static String cpuRangeLabel() {
        return "$" + hex4(cpuBase) + "-$FFFF";
    }

    private static String labelForOffset(int ofs) {
        if (mapperNumber == MAPPER_MMC1) {
            return "L" + hex1(bankNumberForOffset(ofs)) + hex4(offsetToCpu(ofs));
        }
        return "L" + hex4(offsetToCpu(ofs));
    }

    private static int readCpuAddress(int ofs) {
        return ((ROM[ofs+1] & 0xFF) << 8) | (ROM[ofs] & 0xFF);
    }

    // instruction mnemonics
    private static String[] mnemonicLookup = {
        "BRK","ORA","???","???","???","ORA","ASL","???","PHP","ORA","ASL","???","???","ORA","ASL","???",
        "BPL","ORA","???","???","???","ORA","ASL","???","CLC","ORA","???","???","???","ORA","ASL","???",
        "JSR","AND","???","???","BIT","AND","ROL","???","PLP","AND","ROL","???","BIT","AND","ROL","???",
        "BMI","AND","???","???","???","AND","ROL","???","SEC","AND","???","???","???","AND","ROL","???",
        "RTI","EOR","???","???","???","EOR","LSR","???","PHA","EOR","LSR","???","JMP","EOR","LSR","???",
        "BVC","EOR","???","???","???","EOR","LSR","???","CLI","EOR","???","???","???","EOR","LSR","???",
        "RTS","ADC","???","???","???","ADC","ROR","???","PLA","ADC","ROR","???","JMP","ADC","ROR","???",
        "BVS","ADC","???","???","???","ADC","ROR","???","SEI","ADC","???","???","???","ADC","ROR","???",
        "???","STA","???","???","STY","STA","STX","???","DEY","???","TXA","???","STY","STA","STX","???",
        "BCC","STA","???","???","STY","STA","STX","???","TYA","STA","TXS","???","???","STA","???","???",
        "LDY","LDA","LDX","???","LDY","LDA","LDX","???","TAY","LDA","TAX","???","LDY","LDA","LDX","???",
        "BCS","LDA","???","???","LDY","LDA","LDX","???","CLV","LDA","TSX","???","LDY","LDA","LDX","???",
        "CPY","CMP","???","???","CPY","CMP","DEC","???","INY","CMP","DEX","???","CPY","CMP","DEC","???",
        "BNE","CMP","???","???","???","CMP","DEC","???","CLD","CMP","???","???","???","CMP","DEC","???",
        "CPX","SBC","???","???","CPX","SBC","INC","???","INX","SBC","NOP","???","CPX","SBC","INC","???",
        "BEQ","SBC","???","???","???","SBC","INC","???","SED","SBC","???","???","???","SBC","INC","???"
    };
    private static final boolean[] PROCESSABLE_OPCODE = createProcessableOpcodeTable();

    // timing info... not used
    private static int[] opcycleLookup = {
        7, 6, 0, 0, 0, 3, 5, 0, 3, 2, 2, 0, 0, 4, 6, 0,
        2, 5, 0, 0, 0, 4, 6, 0, 2, 4, 0, 0, 0, 4, 7, 0,
        6, 6, 0, 0, 3, 3, 5, 0, 4, 2, 2, 0, 4, 4, 6, 0,
        2, 5, 0, 0, 0, 4, 6, 0, 2, 4, 0, 0, 0, 4, 7, 0,
        6, 6, 0, 0, 0, 3, 5, 0, 3, 2, 2, 0, 3, 4, 6, 0,
        2, 5, 0, 0, 0, 4, 6, 0, 2, 4, 0, 0, 0, 4, 7, 0,
        6, 6, 0, 0, 0, 3, 5, 0, 4, 2, 2, 0, 5, 4, 6, 0,
        2, 5, 0, 0, 0, 4, 6, 0, 2, 4, 0, 0, 0, 4, 7, 0,
        0, 6, 0, 0, 3, 3, 3, 0, 2, 0, 2, 0, 4, 4, 4, 0,
        2, 6, 0, 0, 4, 4, 4, 0, 2, 5, 2, 0, 0, 5, 0, 0,
        2, 6, 2, 0, 3, 3, 3, 0, 2, 2, 2, 0, 4, 4, 4, 0,
        2, 5, 0, 0, 4, 4, 4, 0, 2, 4, 2, 0, 4, 4, 4, 0,
        2, 6, 0, 0, 3, 3, 5, 0, 2, 2, 2, 0, 4, 4, 6, 0,
        2, 5, 0, 0, 0, 4, 6, 0, 2, 4, 0, 0, 0, 4, 7, 0,
        2, 6, 0, 0, 3, 3, 5, 0, 2, 2, 2, 0, 4, 4, 6, 0,
        2, 5, 0, 0, 0, 4, 6, 0, 2, 4, 0, 0, 0, 4, 7, 0
    };

    // length of opcodes
    private static int[] oplengthLookup = {
        1, 2, 0, 0, 0, 2, 2, 0, 1, 2, 1, 0, 0, 3, 3, 0,
        2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 0, 0, 0, 3, 3, 0,
        3, 2, 0, 0, 2, 2, 2, 0, 1, 2, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 0, 0, 0, 3, 3, 0,
        1, 2, 0, 0, 0, 2, 2, 0, 1, 2, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 0, 0, 0, 3, 3, 0,
        1, 2, 0, 0, 0, 2, 2, 0, 1, 2, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 0, 0, 0, 3, 3, 0,
        0, 2, 0, 0, 2, 2, 2, 0, 1, 1, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 2, 2, 2, 0, 1, 3, 1, 0, 0, 3, 0, 0,
        2, 2, 2, 0, 2, 2, 2, 0, 1, 2, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 2, 2, 2, 0, 1, 3, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 2, 2, 2, 0, 1, 2, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 0, 0, 0, 3, 3, 0,
        2, 2, 0, 0, 2, 2, 2, 0, 1, 2, 1, 0, 3, 3, 3, 0,
        2, 2, 0, 0, 0, 2, 2, 0, 1, 3, 0, 0, 0, 3, 3, 0
    };

    // address modes for opcodes
    private static int[] opaddrmodeLookup = {
        UNDF, INDX, UNDF, UNDF, UNDF, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, UNDF, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, UNDF, ZERX, ZERX, UNDF,
        IMPL, ABSY, UNDF, UNDF, UNDF, ABSX, ABSX, UNDF,
        ABSL, INDX, UNDF, UNDF, ZERO, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, ABSL, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, UNDF, ZERX, ZERX, UNDF,
        IMPL, ABSY, UNDF, UNDF, UNDF, ABSX, ABSX, UNDF,
        IMPL, INDX, UNDF, UNDF, UNDF, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, ABSL, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, UNDF, ZERX, ZERX, UNDF,
        IMPL, ABSY, UNDF, UNDF, UNDF, ABSX, ABSX, UNDF,
        IMPL, INDX, UNDF, UNDF, UNDF, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, INDR, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, UNDF, ZERX, ZERX, UNDF,
        IMPL, ABSY, UNDF, UNDF, UNDF, ABSX, ABSX, UNDF,
        UNDF, INDX, UNDF, UNDF, ZERO, ZERO, ZERO, UNDF,
        IMPL, UNDF, IMPL, UNDF, ABSL, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, ZERX, ZERX, ZERY, UNDF,
        IMPL, ABSY, IMPL, UNDF, UNDF, ABSX, UNDF, UNDF,
        IMMD, INDX, IMMD, UNDF, ZERO, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, ABSL, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, ZERX, ZERX, ZERY, UNDF,
        IMPL, ABSY, IMPL, UNDF, ABSX, ABSX, ABSY, UNDF,
        IMMD, INDX, UNDF, UNDF, ZERO, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, ABSL, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, UNDF, ZERX, ZERX, UNDF,
        IMPL, ABSY, UNDF, UNDF, UNDF, ABSX, ABSX, UNDF,
        IMMD, INDX, UNDF, UNDF, ZERO, ZERO, ZERO, UNDF,
        IMPL, IMMD, IMPL, UNDF, ABSL, ABSL, ABSL, UNDF,
        RELV, INDY, UNDF, UNDF, UNDF, ZERX, ZERX, UNDF,
        IMPL, ABSY, UNDF, UNDF, UNDF, ABSX, ABSX, UNDF
    };

    // to speed up conversion from bin to ascii...
    private static String[] hexLookup = {
        "00", "01", "02", "03", "04", "05", "06", "07",
        "08", "09", "0A", "0B", "0C", "0D", "0E", "0F",
        "10", "11", "12", "13", "14", "15", "16", "17",
        "18", "19", "1A", "1B", "1C", "1D", "1E", "1F",
        "20", "21", "22", "23", "24", "25", "26", "27",
        "28", "29", "2A", "2B", "2C", "2D", "2E", "2F",
        "30", "31", "32", "33", "34", "35", "36", "37",
        "38", "39", "3A", "3B", "3C", "3D", "3E", "3F",
        "40", "41", "42", "43", "44", "45", "46", "47",
        "48", "49", "4A", "4B", "4C", "4D", "4E", "4F",
        "50", "51", "52", "53", "54", "55", "56", "57",
        "58", "59", "5A", "5B", "5C", "5D", "5E", "5F",
        "60", "61", "62", "63", "64", "65", "66", "67",
        "68", "69", "6A", "6B", "6C", "6D", "6E", "6F",
        "70", "71", "72", "73", "74", "75", "76", "77",
        "78", "79", "7A", "7B", "7C", "7D", "7E", "7F",
        "80", "81", "82", "83", "84", "85", "86", "87",
        "88", "89", "8A", "8B", "8C", "8D", "8E", "8F",
        "90", "91", "92", "93", "94", "95", "96", "97",
        "98", "99", "9A", "9B", "9C", "9D", "9E", "9F",
        "A0", "A1", "A2", "A3", "A4", "A5", "A6", "A7",
        "A8", "A9", "AA", "AB", "AC", "AD", "AE", "AF",
        "B0", "B1", "B2", "B3", "B4", "B5", "B6", "B7",
        "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF",
        "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7",
        "C8", "C9", "CA", "CB", "CC", "CD", "CE", "CF",
        "D0", "D1", "D2", "D3", "D4", "D5", "D6", "D7",
        "D8", "D9", "DA", "DB", "DC", "DD", "DE", "DF",
        "E0", "E1", "E2", "E3", "E4", "E5", "E6", "E7",
        "E8", "E9", "EA", "EB", "EC", "ED", "EE", "EF",
        "F0", "F1", "F2", "F3", "F4", "F5", "F6", "F7",
        "F8", "F9", "FA", "FB", "FC", "FD", "FE", "FF"
    };

/**
* Main.
**/

    public static void main(String[] args) throws Exception {
        if (args.length == 0) {
            printUsage();
            System.exit(1);
        }
        File f = new File(args[0]);
        if (f==null || !f.canRead()) {
            exitWithError("Error: Couldn't read " + args[0] + ".");
        }
        int cliMapper = parseMapperOption(args);
        configurePrgMapping(f.length(), cliMapper);
        name = f.getName();

        // Reset lifted state in case a prior invocation populated it.
        codePointersStart = new ArrayList<Integer>();
        codePointersCount = new ArrayList<Integer>();
        dataPointersStart = new ArrayList<Integer>();
        dataPointersCount = new ArrayList<Integer>();
        codeEntries = new ArrayList<Integer>();
        knownCallsites = new TreeMap<Integer, ResolvedRecord>();
        inlineCalls = InlineCallsConfig.EMPTY;
        dataRanges = DataRangesConfig.EMPTY;
        // parse rest of arguments
        for (int i=1; i<args.length; i++) {
            if (args[i].equals("-html")) {
                toHtml = true;
            }
            else if (args[i].equals("-mapper")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing mapper number after -mapper.");
                }
                // Already applied before PRG-size validation.
                ++i;
            }
            else if (args[i].equals("-codeentries")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing filename after -codeentries.");
                }
                File configFile = new File(args[i+1]);
                if (!configFile.canRead()) {
                    exitWithError("Error: Couldn't read " + args[i+1] + ".");
                }
                try (BufferedReader br = new BufferedReader(new FileReader(configFile))) {
                    String line;
                    int lineNo = 0;
                    while ((line = br.readLine()) != null) {
                        lineNo++;
                        line = stripConfigComments(line).trim();
                        if (line.length() == 0) {
                            continue;
                        }
                        if (line.equalsIgnoreCase("addr") || line.equalsIgnoreCase("bank|addr")) {
                            continue;
                        }
                        String[] parts = line.split("\\|", -1);
                        if (parts.length != 1 && parts.length != 2) {
                            exitWithError("Error: Bad codeentries config format at line " + lineNo + ": " + line);
                        }
                        int target;
                        try {
                            if (parts.length == 1) {
                                int cpuAddr = parseCpuAddress("codeentries", parts[0].trim(), lineNo);
                                target = cpuToPrgOffset(cpuAddr);
                            } else {
                                target = parseBankedPrgOffset(
                                    "codeentries", parts[0].trim(), parts[1].trim(), lineNo);
                            }
                        } catch (ConfigException ex) {
                            exitWithError("Error: " + ex.getMessage());
                            return;
                        }
                        codeEntries.add(target);
                    }
                }
                ++i;
            }
            else if (args[i].equals("-codepointers")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing filename after -codepointers.");
                }
                parsePointerTableConfig(args[i+1], "code pointer", codePointersStart, codePointersCount);
                ++i;
            }
            else if (args[i].equals("-datapointers")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing filename after -datapointers.");
                }
                parsePointerTableConfig(args[i+1], "data pointer", dataPointersStart, dataPointersCount);
                ++i;
            }
            else if (args[i].equals("-inlinecalls")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing filename after -inlinecalls.");
                }
                try {
                    inlineCalls = InlineCallsConfig.parse(args[i+1]);
                } catch (ConfigException ex) {
                    exitWithError("Error: " + ex.getMessage());
                }
                ++i;
            }
            else if (args[i].equals("-dataranges")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing filename after -dataranges.");
                }
                try {
                    dataRanges = DataRangesConfig.parse(args[i+1]);
                } catch (ConfigException ex) {
                    exitWithError("Error: " + ex.getMessage());
                }
                ++i;
            }
            else {
                exitWithError("Bad argument: " + args[i]);
            }
        }

	// read file
        ROM = new int[(int)f.length()];
        try (FileInputStream fis = new FileInputStream(f)) {
            for (int i=0; i<ROM.length; i++) {
                int value = fis.read();
                if (value < 0) {
                    exitWithError("Error: Unexpected EOF while reading ROM.");
                }
                ROM[i] = value;
            }
        }

        // Allocate the code/data map once; runAnalysisPass clears it on every
        // restart pass.
        map = new int[ROM.length];

        // User-provided code-pointer table count, captured before appending the
        // 6502 fixed-vector table at the PRG tail. Only user-provided tables get a
        // label at their start; vector targets are still labelled like any other
        // code-pointer target so the fixed-vector .DW entries stay symbolic.
        appendFixedVectorTable();

        try {
            runAnalysisToFixedPoint();
        } catch (ConfigException ex) {
            exitWithError("Error: " + ex.getMessage());
        }
        verifyDataLabels();
        disassemble();
        //
        System.exit(0);
    }

/**
* Runs analysis passes until no new inline callsites are discovered. Each
* restart promotes the pass's discoveries into knownCallsites so the next
* pass can block their record bytes and seed their continuations.
* Termination is guaranteed because each restart adds at least one
* previously unknown callsite and the ROM is finite. A safety cap converts
* a runaway loop into a catchable configuration failure.
**/

    public static void runAnalysisToFixedPoint() {
        int passNo = 0;
        while (true) {
            runAnalysisPass();
            passNo++;
            if (newlyDiscoveredCallsites.isEmpty()) {
                return;
            }
            for (Integer callsite : newlyDiscoveredCallsites) {
                int jsrTarget = getAddressForContext(callsite + 1, callsite);
                InlineCallEntry entry = inlineCalls.findForCallsite(callsite, jsrTarget);
                knownCallsites.put(callsite, resolveRecord(callsite, entry));
            }
            if (passNo > analysisPassLimit) {
                throw new ConfigException("inline-call discovery did not converge after "
                    + passNo + " passes.");
            }
        }
    }

    private static void appendFixedVectorTable() {
        userCodePointersCount = codePointersStart.size();
        codePointersStart.add(prgSize - 6);
        codePointersCount.add(3);
    }

/**
* One full analysis pass per §7.2 of the inline-call recovery spec: rebuild
* the role map and the blocked-from-code mask, apply data ranges and
* resolved inline records, then apply user-provided pointer tables, data
* pointer tables, and code entries. processCode runs as a side effect of
* each seed, so by return the map reflects everything reachable under the
* current set of known callsites.
**/

    public static void runAnalysisPass() {
        newlyDiscoveredCallsites = new LinkedHashSet<Integer>();
        for (int i = 0; i < map.length; i++) {
            map[i] = DATA;
        }
        blockedFromCode = new boolean[ROM.length];

        // Phase 1: build the complete blocked-from-code mask BEFORE any seed
        // is queued. Interleaving block-and-seed (per range / per record)
        // would let an earlier continuation trace into a later barrier whose
        // bytes haven't yet been blocked, decoding them as instructions on
        // this pass and producing nondeterministic per-pass artifacts.
        blockDataRanges();
        blockKnownInlineRecords();

        // Phase 2: labels and seeds. Every barrier is now in place, so
        // processCode calls below cannot accidentally walk into a not-yet-
        // blocked range or record.
        labelAndSeedDataRanges();
        labelAndSeedKnownInlineRecords();

        // mark the code pointer table bytes
        for (int i = 0; i < codePointersStart.size(); ++i) {
            int offset = codePointersStart.get(i);
            int count = codePointersCount.get(i);
            String source = (i >= userCodePointersCount)
                ? "fixed vector table at $" + cpuLabel(offset)
                : "code-pointer table at $" + cpuLabel(offset);
            markPointerTableBytes(offset, count, source);
        }

        // process code pointers recursively
        for (int i = 0; i < codePointersStart.size(); ++i) {
            int offset = codePointersStart.get(i);
            int count = codePointersCount.get(i);
            // Label the start of the explicit pointer table so the .DW run is
            // anchored at its own LXXXX: label instead of trailing the previous
            // routine anonymously. Skip the auto-added fixed-vector table.
            if (count > 0 && i < userCodePointersCount) {
                map[offset] |= LABEL;
            }
            boolean isVectorTable = (i >= userCodePointersCount);
            for (int j = 0; j < count; ++j) {
                int pointerOffset = offset + j*2;
                ArrayList<Integer> targets = codePointerTargetsForContext(pointerOffset, pointerOffset);
                if (targets.isEmpty()) {
                    continue;
                }
                // Every ROM-window code-pointer target gets a label, even if
                // processCode can't decode the bytes there.
                for (Integer target : targets) {
                    if (blockedFromCode[target]) {
                        String source = isVectorTable
                            ? "fixed vector at $" + cpuLabel(pointerOffset)
                            : "code-pointer table at $" + cpuLabel(offset) + " entry [" + j + "]";
                        failBlockedConflict(target, source);
                    }
                    map[target] |= LABEL;
                    processCode(target);
                }
            }
        }

        // mark data pointer table bytes; targets get labels but are NOT traced as code
        for (int i = 0; i < dataPointersStart.size(); ++i) {
            int offset = dataPointersStart.get(i);
            int count = dataPointersCount.get(i);
            markPointerTableBytes(offset, count, "data-pointer table at $" + cpuLabel(offset));
            for (int j = 0; j < count; ++j) {
                int pointerOffset = offset + j*2;
                if (!isROMAddress(pointerOffset, pointerOffset)) {
                    continue;
                }
                int target = getAddressForContext(pointerOffset, pointerOffset);
                map[target] |= LABEL;
            }
            // Label the table start AFTER the byte-marking loop, since the j=0 store
            // above would otherwise clobber any earlier LABEL bit on map[offset].
            if (count > 0) {
                map[offset] |= LABEL;
            }
        }

        // process direct code entries (CPU addresses already converted to PRG offsets)
        for (int i = 0; i < codeEntries.size(); ++i) {
            int target = codeEntries.get(i);
            if (blockedFromCode[target]) {
                failBlockedConflict(target, "codeentries entry [" + i + "] -> $" + cpuLabel(target));
            }
            map[target] |= LABEL;
            processCode(target);
        }
    }

    private static void markPointerTableBytes(int offset, int count, String source) {
        for (int j = 0; j < count; ++j) {
            for (int b = 0; b < 2; ++b) {
                int byteOffset = offset + j*2 + b;
                if (blockedFromCode[byteOffset]) {
                    failBlockedConflict(byteOffset, source + " entry [" + j + "] byte [" + b + "]");
                }
                map[byteOffset] = CODE | PTR;
            }
        }
    }

/**
* Phase-1 mask construction for resolved inline records. Marks every record
* byte as blocked-from-code and detects record-vs-record / record-vs-range
* overlaps. Does NOT label anything or seed continuations — that is phase
* 2's job, after every record AND every data range has been added to the
* mask.
**/

    public static void blockKnownInlineRecords() {
        for (ResolvedRecord r : knownCallsites.values()) {
            for (int i = r.recordStart; i < r.recordEnd; i++) {
                if (i < blockedFromCode.length && blockedFromCode[i]) {
                    String blocking = findBlockingSource(i);
                    throw new ConfigException("inline record at callsite $" + cpuLabel(r.callsite)
                        + " -> $" + hex4(r.entry.calleeCpu)
                        + " overlaps already-blocked byte $" + cpuLabel(i)
                        + " (" + blocking + ")");
                }
                blockedFromCode[i] = true;
            }
        }
    }

/**
* Phase-2 label + seed for resolved inline records. Labels record_start,
* labels and seeds adjusted code-pointer targets, labels adjusted data-
* pointer targets without seeding them, and labels + seeds record_end as a
* code continuation. Must run only after blockKnownInlineRecords and
* blockDataRanges have populated the complete barrier mask.
**/

    public static void labelAndSeedKnownInlineRecords() {
        for (ResolvedRecord r : knownCallsites.values()) {
            if (inPrgOffset(r.recordStart)) {
                map[r.recordStart] |= LABEL;
            }
            InlineField[] fields = r.entry.layout.fields;
            for (int k = 0; k < fields.length; k++) {
                InlineField field = fields[k];
                if (field.kind != InlineField.PTR16) {
                    continue;
                }
                int target = r.pointerTargets[k];
                if (!inPrgOffset(target)) {
                    continue;
                }
                if (field.pointerKind == PointerKind.CODE && blockedFromCode[target]) {
                    failBlockedConflict(target, "inline ptr16(code) at callsite $"
                        + cpuLabel(r.callsite) + " field " + k);
                }
                map[target] |= LABEL;
                if (field.pointerKind == PointerKind.CODE) {
                    processCode(target);
                }
            }
            if (inPrgOffset(r.recordEnd)) {
                if (blockedFromCode[r.recordEnd]) {
                    failBlockedConflict(r.recordEnd, "inline record continuation at callsite $"
                        + cpuLabel(r.callsite));
                }
                map[r.recordEnd] |= LABEL;
                processCode(r.recordEnd);
            }
        }
    }

/**
* Convenience composite used by single-record / single-range tests. Runs
* block + label/seed back-to-back; runAnalysisPass uses the split phase
* methods directly so all barriers are constructed before any seed traces.
**/

    public static void applyKnownInlineRecords() {
        blockKnownInlineRecords();
        labelAndSeedKnownInlineRecords();
    }

/**
* Describes which configured data range or resolved inline record blocks a
* given PRG offset. Used to format the "blocked by" line in conflict
* diagnostics. Returns a generic stub when no source can be identified —
* that should never happen if the mask was built consistently.
**/

    static String findBlockingSource(int target) {
        for (int k = 0; k < dataRanges.entries.length; k++) {
            DataRangeEntry r = dataRanges.entries[k];
            if (target >= r.start && target < r.end) {
                return "data range $" + hex4(r.startCpu) + "-$"
                    + hex4(r.startCpu + r.length - 1)
                    + " (dataranges config line " + r.sourceLine + ")";
            }
        }
        for (ResolvedRecord r : knownCallsites.values()) {
            if (target >= r.recordStart && target < r.recordEnd) {
                return "inline record at callsite $" + cpuLabel(r.callsite)
                    + " -> $" + hex4(r.entry.calleeCpu)
                    + " (inlinecalls config line " + r.entry.sourceLine + ")"
                    + " (record $" + cpuLabel(r.recordStart) + "-$"
                    + cpuLabel(r.recordEnd - 1) + ")";
            }
        }
        return "blocked byte (source unknown)";
    }

    static void failBlockedConflict(int target, String source) {
        String blocking = findBlockingSource(target);
        throw new ConfigException("inline-data conflict at $" + cpuLabel(target)
            + "; blocked by " + blocking + "; conflicting target: " + source);
    }

/**
* Resolves a single inline record at the given callsite against its
* configured layout. Validates the JSR encoding, walks each field, evaluates
* counted8 payload size from ROM, and computes adjusted pointer targets.
* Throws ConfigException on any out-of-ROM or pointer-out-of-range condition.
**/

    public static ResolvedRecord resolveRecord(int callsite, InlineCallEntry entry) {
        if (callsite + 3 > prgSize) {
            throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                + " (callee $" + hex4(entry.calleeCpu) + "): JSR extends past end of ROM");
        }
        if (ROM[callsite] != 0x20) {
            throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                + ": expected JSR ($20), got $" + hex2(ROM[callsite]));
        }
        int actualTarget = getAddressForContext(callsite + 1, callsite);
        if (actualTarget != entry.callee) {
            throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                + ": JSR target $" + cpuLabel(actualTarget) + " does not match configured callee $"
                + hex4(entry.calleeCpu));
        }
        InlineField[] fields = entry.layout.fields;
        int[] fieldStarts = new int[fields.length];
        int[] fieldEnds = new int[fields.length];
        int[] pointerTargets = new int[fields.length];
        for (int k = 0; k < pointerTargets.length; k++) {
            pointerTargets[k] = -1;
        }
        int recordStart = callsite + 3;
        int ofs = recordStart;
        for (int k = 0; k < fields.length; k++) {
            InlineField field = fields[k];
            fieldStarts[k] = ofs;
            int fieldSize;
            if (field.kind == InlineField.COUNTED8) {
                if (ofs >= prgSize) {
                    throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                        + " (callee $" + hex4(entry.calleeCpu) + "): counted8 count byte past end of ROM");
                }
                int count = ROM[ofs];
                fieldSize = 1 + count;
                if (ofs + fieldSize > prgSize) {
                    throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                        + " (callee $" + hex4(entry.calleeCpu) + "): counted8 payload of " + count
                        + " bytes exceeds ROM");
                }
            } else if (field.kind == InlineField.PTR16) {
                if (ofs + 2 > prgSize) {
                    throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                        + " (callee $" + hex4(entry.calleeCpu) + "): ptr16 extends past end of ROM");
                }
                int encoded = readCpuAddress(ofs);
                int adjustedTarget = (encoded + field.pointerAdjustment) & 0xFFFF;
                if (!isStaticallyMappedCpuAddress(adjustedTarget, callsite)) {
                    throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                        + " (callee $" + hex4(entry.calleeCpu) + "): adjusted pointer target $"
                        + hex4(adjustedTarget) + " is outside canonical ROM space "
                        + cpuRangeLabel());
                }
                pointerTargets[k] = cpuToPrgOffsetForContext(adjustedTarget, callsite);
                fieldSize = 2;
            } else {
                fieldSize = field.byteCount;
                if (ofs + fieldSize > prgSize) {
                    throw new ConfigException("inline record at callsite $" + cpuLabel(callsite)
                        + " (callee $" + hex4(entry.calleeCpu) + "): field " + k + " extends past end of ROM");
                }
            }
            ofs += fieldSize;
            fieldEnds[k] = ofs;
        }
        int recordEnd = ofs;
        return new ResolvedRecord(callsite, entry, recordStart, recordEnd, fieldStarts, fieldEnds, pointerTargets);
    }

    private static String cpuLabel(int prgOffset) {
        int normalized = normalizePrgOffset(prgOffset);
        if (!inPrgOffset(normalized)) {
            return hex4(offsetToCpu(prgOffset));
        }
        return hex4(offsetToCpu(normalized));
    }

    private static String hex2(int b) {
        String s = Integer.toHexString(b & 0xFF).toUpperCase();
        return s.length() == 1 ? "0" + s : s;
    }

    private static String hex1(int b) {
        return Integer.toHexString(b & 0x0F).toUpperCase();
    }

/**
* Returns PRG offset made up by the two bytes at offset ofs in the ROM.
**/

    public static int getAddress(int ofs) {
        return getAddressForContext(ofs, ofs);
    }

    private static int getAddressForContext(int ofs, int contextOfs) {
        return cpuToPrgOffsetForContext(readCpuAddress(ofs), contextOfs);
    }

/**
* Iteratively maps code reachable from an entry offset using a worklist.
* Returns true if any new code bytes were mapped.
**/

    public static boolean processCode(int ofs) {
        queueCodeTarget(ofs);
        if (processCodeActive) {
            return false;
        }
        boolean mappedAny = false;
        processCodeActive = true;
        try {
            while (!codeWorklist.isEmpty()) {
                int target = (int)codeWorklist.removeFirst();
                if (processCodeSingle(target)) {
                    mappedAny = true;
                }
            }
        } finally {
            processCodeActive = false;
            codeWorklist.clear();
        }
        return mappedAny;
    }

    private static void queueCodeTarget(int ofs) {
        // Normalize to PRG-ROM address space to avoid out-of-range map access.
        int target = normalizePrgOffset(ofs);
        if (isTraceablePrgOffset(target)) {
            codeWorklist.addLast(target);
        }
    }

    private static void queueRelativeBranchTarget(int ofs) {
        int target = relativeBranchTarget(ofs);
        if (target < 0 || !isTraceablePrgOffset(target)) {
            return;
        }
        if (blockedFromCode[target]) {
            failBlockedConflict(target, "relative branch at $" + cpuLabel(ofs));
        }
        queueCodeTarget(target);
    }

    private static int relativeBranchTarget(int ofs) {
        int dist = ROM[ofs+1];
        int signed = (dist < 0x80) ? dist : -(((dist ^ 0xFF) + 1) & 0xFF);
        if (mapperNumber == MAPPER_MMC1) {
            int cpuTarget = (offsetToCpu(ofs) + 2 + signed) & 0xFFFF;
            if (!isStaticallyMappedCpuAddress(cpuTarget, ofs)) {
                return -1;
            }
            return cpuToPrgOffsetForContext(cpuTarget, ofs);
        }
        return normalizePrgOffset(ofs + 2 + signed);
    }

    private static boolean processCodeSingle(int ofs) {
        if (isCode(ofs) && !isInstr(ofs)) {
            return false;
        }
        boolean done=false, jsrchk=false;
        int op, len;
        int chkpt=ofs;  // initialize checkpoint to current offset
        int startofs=ofs;
        // Stop linearly at any byte explicitly blocked from code (configured
        // data range or resolved inline-record byte). Fallthrough into the
        // first byte of a blocked range ends the linear path without decoding
        // the blocked byte itself.
        while (!done && isData(ofs) && !blockedFromCode[ofs]) {
            // process one opcode
            op = ROM[ofs];
            len = oplengthLookup[op];
            if (len > 0) {
                if ((ofs + len) > map.length) {
                    return false;
                }
                // The opcode byte was unblocked (loop guard above), but the
                // instruction's operand bytes might still cross into a barrier.
                // Marking them as code would silently override the explicit
                // data claim — spec §8 requires this to be a conflict.
                for (int i = 1; i < len; i++) {
                    if (blockedFromCode[ofs + i]) {
                        failBlockedConflict(ofs + i,
                            "operand of instruction at $" + cpuLabel(ofs));
                    }
                }
                map[ofs] &= NOT_DATA;
                map[ofs] |= INSTR | CODE;   // 1st byte of instruction
                // mark the operand bytes as code too
                for (int i=1; i<len; i++) {
                    map[ofs+i] &= NOT_DATA;
                    map[ofs+i] &= NOT_INSTR;
                    map[ofs+i] &= NOT_LABEL;
                    map[ofs+i] |= CODE;
                }
            }
            if (!PROCESSABLE_OPCODE[op]) {   // Bad opcode
                while (ofs >= chkpt) {
                    map[ofs] &= NOT_CODE;
                    map[ofs] &= NOT_INSTR;
                    map[ofs--] |= DATA;
                }
                ofs++;
                if (jsrchk) {   // process jump table
                    while ((ofs + 1 < map.length) && (map[ofs] == DATA)
                        && isCanonicalROMAddress(ofs, ofs)) {
                        queueCodeTarget(getAddressForContext(ofs, ofs));
                        map[ofs++] = CODE | PTR;
                        map[ofs++] = CODE | PTR;
                    }
                }
                done = true;
            }

            if (!done && CHECK_DATA_LABEL_OPCODE[op]) {
                checkDataLabel(ofs+1, ofs);
            }

            if (!done && RELATIVE_BRANCH_OPCODE[op]) {
                queueRelativeBranchTarget(ofs);
                chkpt = ofs+2;
                jsrchk = false;
                ofs += len;
                continue;
            }

            switch (op) {
                case 0x20: {  // JSR
                    boolean romTarget = isROMAddress(ofs+1, ofs);
                    if (romTarget) {
                        int jsrTarget = getAddressForContext(ofs+1, ofs);
                        if (blockedFromCode[jsrTarget]) {
                            failBlockedConflict(jsrTarget, "JSR at $" + cpuLabel(ofs));
                        }
                        queueCodeTarget(jsrTarget);
                        InlineCallEntry inlineEntry = inlineCalls.findForCallsite(ofs, jsrTarget);
                        if (inlineEntry != null) {
                            // Configured inline call: record the callsite if new
                            // and terminate the linear path. The record bytes are
                            // (or will be) blocked, and record_end is (or will be)
                            // a separate code seed, so falling through here would
                            // either decode garbage or violate the barrier.
                            if (!knownCallsites.containsKey(ofs)) {
                                newlyDiscoveredCallsites.add(ofs);
                            }
                            done = true;
                            break;
                        }
                    }
                    chkpt = ofs+3;
                    jsrchk = romTarget;
                    break;
                }

                case 0x40:  // RTI
                case 0x60:  // RTS
                    done = true;
                    break;

                case 0x4C: {  // JMP Abs
                    if (isROMAddress(ofs+1, ofs)) {
                        int jmpTarget = getAddressForContext(ofs+1, ofs);
                        if (blockedFromCode[jmpTarget]) {
                            failBlockedConflict(jmpTarget, "JMP at $" + cpuLabel(ofs));
                        }
                        queueCodeTarget(jmpTarget);
                    }
                    done = true;
                    break;
                }

                case 0x6C: {  // JMP Ind
                    if (isROMAddress(ofs+1, ofs)) {
                        int vectorOffset = getAddressForContext(ofs+1, ofs);
                        if ((vectorOffset + 1 < map.length) && isROMAddress(vectorOffset, vectorOffset)) {
                            int indTarget = getAddressForContext(vectorOffset, vectorOffset);
                            if (blockedFromCode[indTarget]) {
                                failBlockedConflict(indTarget, "JMP indirect via $" + cpuLabel(ofs));
                            }
                            queueCodeTarget(indTarget);
                        }
                    }
                    done = true;
                    break;
                }

                default:
                    break;
            }   // switch
            ofs += len;
        }   // while
        if ((ofs != startofs) || isCode(startofs)) {
            map[startofs] |= LABEL;
        }
        return (ofs != startofs);   // true if new code was mapped, false otherwise
    }

/**
* Use the ROM & map to output a (possible HTML) formatted disassembly.
**/

    public static void disassemble() {
        if (toHtml) {
            System.out.println("<HTML>");
            System.out.println("<BODY>");
            System.out.println("<FONT FACE=\"Courier\">");
        }
        // Precompute output-time indices from the resolved analysis state.
        // recordsByStart maps a record_start PRG offset to its resolved record;
        // dataBoundaries holds every start/end offset of a record or a data
        // range so the .DB walker can break runs at those boundaries (spec §9.2).
        recordsByStart = new HashMap<Integer, ResolvedRecord>();
        dataBoundaries = new TreeSet<Integer>();
        for (ResolvedRecord r : knownCallsites.values()) {
            recordsByStart.put(r.recordStart, r);
            dataBoundaries.add(r.recordStart);
            dataBoundaries.add(r.recordEnd);
        }
        for (int k = 0; k < dataRanges.entries.length; k++) {
            DataRangeEntry e = dataRanges.entries[k];
            dataBoundaries.add(e.start);
            dataBoundaries.add(e.end);
        }
        addBankBoundaries();
        //
        int ofs = 0, op, amode;
        while (ofs < prgSize) {
            maybeEmitOrg(ofs);
            if (isCode(ofs)) {
                if (isPtr(ofs)) {   // print jump table
                    newLine();
                    if (isLabel(ofs)) {
                        String tableLabel = labelForOffset(ofs);
                        if (toHtml)
                            System.out.print("<A NAME="+tableLabel+">");
                        System.out.print(tableLabel+":");
                        newLine();
                    }
                    while ((ofs < prgSize) && isPtr(ofs)) {
                        System.out.print(".DW ");
                        // Only emit a label form when the pointer bytes are in the canonical
                        // project ROM range. For NROM-128 mirror operands, or MMC1 switchable
                        // bank operands, a plain CPU address is not a unique output label.
                        // Match the canonical-output guard used in printAddress().
                        if (isCanonicalROMAddress(ofs, ofs) && isLabel(getAddressForContext(ofs, ofs))) {
                            printLabel(labelForOffset(getAddressForContext(ofs, ofs)));
                        }
                        else {
                            System.out.print("$"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
                        }
                        newLine();
                        ofs += 2;
                    }
                    newLine();
                }
                else {
                    if (isLabel(ofs)) {
                        String label = labelForOffset(ofs);
                        if (toHtml)
                            System.out.print("<A NAME="+label+">");
                        System.out.print(label+":");
                        newLine();
                    }
                    op = ROM[ofs];
                    if (toHtml)
                        System.out.print("&nbsp;&nbsp;&nbsp;&nbsp;");
                    else
                        System.out.print("    ");
                    if ((oplengthLookup[op] <= 0) || (opaddrmodeLookup[op] == UNDF)) {
                        System.out.print(".DB $"+hexLookup[op]);
                        newLine();
                        ofs++;
                        continue;
                    }
                    System.out.print(mnemonicLookup[op]);
                    amode = opaddrmodeLookup[op];
                    if (amode == IMPL) {
                        newLine();
                        if ((op == 0x40) || (op == 0x60) || (op == 0x4C)) {
                            newLine();
                        }
                    }
                    else if (amode == IMMD) {
                        System.out.print(" #$"+hexLookup[ROM[ofs+1]]);
                        newLine();
                    }
                    else if (amode == ZERO) {
                        System.out.print(" $"+hexLookup[ROM[ofs+1]]);
                        newLine();
                    }
                    else if (amode == ZERX) {
                        System.out.print(" $"+hexLookup[ROM[ofs+1]]+",X");
                        newLine();
                    }
                    else if (amode == ZERY) {
                        System.out.println(" $"+hexLookup[ROM[ofs+1]]+",Y");
                    }
                    else if (amode == ABSL) {
                        printAddress(ofs+1, op, ofs);
                        newLine();
                    }
                    else if (amode == ABSX) {
                        printAddress(ofs+1, op, ofs);
                        System.out.print(",X");
                        newLine();
                    }
                    else if (amode == ABSY) {
                        printAddress(ofs+1, op, ofs);
                        System.out.print(",Y");
                        newLine();
                    }
                    else if (amode == INDR) {
                        System.out.print(" [$"+hexLookup[ROM[ofs+2]]+hexLookup[ROM[ofs+1]]+"]");
                        newLine();
                    }
                    else if (amode == INDX) {
                        System.out.print(" [$"+hexLookup[ROM[ofs+1]]+",X]");
                        newLine();
                    }
                    else if (amode == INDY) {
                        System.out.print(" [$"+hexLookup[ROM[ofs+1]]+"],Y");
                        newLine();
                    }
                    else if (amode == RELV) {
                        System.out.print(" ");
                        int addr = relativeBranchTarget(ofs);
                        if (addr >= 0 && isLabel(addr)) {
                            printLabel(labelForOffset(addr));
                        }
                        else {
                            printRelativeLiteral(ofs);
                        }
                        newLine();
                    }
                    ofs += oplengthLookup[op];
                }
            }   // isCode(ofs)
            else if (isData(ofs)) { // print data table
                // If an inline record starts here, emit it field-by-field
                // instead of running a normal .DB block. The label is printed
                // inside emitInlineRecord.
                ResolvedRecord record = recordsByStart.get(ofs);
                if (record != null) {
                    emitInlineRecord(record);
                    ofs = record.recordEnd;
                    newLine();
                    continue;
                }
                if (isLabel(ofs)) {
                    String label = labelForOffset(ofs);
                    if (toHtml)
                        System.out.println("<A NAME="+label+"><BR>");
                    System.out.print(label+":");
                    newLine();
                }
                System.out.print(".DB $"+hexLookup[ROM[ofs++]]);
                int i=1;
                // Stop the .DB run at the next data-block boundary so that
                // configured data ranges and resolved inline records remain
                // distinct from adjacent generic data (spec §9.2).
                while ((ofs < prgSize) && (map[ofs] == DATA) && !dataBoundaries.contains(ofs)) {
                    if ((i++ & 15) == 0) {
                        newLine();
                        System.out.print(".DB ");
                    }
                    else {
                        System.out.print(",");
                    }
                    System.out.print("$"+hexLookup[ROM[ofs++]]);
                    }
                newLine();
                newLine();
            }   // isData(ofs)
        }   // while
        System.out.print(".END");
        newLine();
        if (toHtml) {
            System.out.println("</FONT>");
            System.out.println("</BODY>");
            System.out.println("</HTML>");
        }
    }

    private static void addBankBoundaries() {
        if (mapperNumber != MAPPER_MMC1) {
            return;
        }
        for (int ofs = 0x4000; ofs < prgSize; ofs += 0x4000) {
            dataBoundaries.add(ofs);
        }
    }

    private static void maybeEmitOrg(int ofs) {
        if (mapperNumber == MAPPER_MMC1) {
            if ((ofs & 0x3FFF) != 0) {
                return;
            }
            int org = (ofs >= fixedBankOffset) ? 0xC000 : 0x8000;
            System.out.print(".ORG $" + hex4(org));
            newLine();
            newLine();
            return;
        }
        if (ofs == 0) {
            System.out.print(".ORG $" + hex4(cpuBase));
            newLine();
            newLine();
        }
    }

/**
*
**/

    public static boolean isROMAddress(int ofs) {
        return isROMAddress(ofs, ofs);
    }

    private static boolean isROMAddress(int ofs, int contextOfs) {
        return isStaticallyMappedCpuAddress(readCpuAddress(ofs), contextOfs);
    }

    private static ArrayList<Integer> codePointerTargetsForContext(int ofs, int contextOfs) {
        ArrayList<Integer> targets = new ArrayList<Integer>();
        int cpu = readCpuAddress(ofs);
        if (!isCpuRomAddress(cpu)) {
            return targets;
        }
        if (mapperNumber == MAPPER_MMC1
            && cpu < 0xC000
            && inPrgOffset(contextOfs)
            && contextOfs >= fixedBankOffset) {
            int bankCount = prgSize / 0x4000;
            for (int bank = 0; bank < bankCount - 1; bank++) {
                targets.add((bank * 0x4000) + (cpu - 0x8000));
            }
            return targets;
        }
        if (isStaticallyMappedCpuAddress(cpu, contextOfs)) {
            targets.add(cpuToPrgOffsetForContext(cpu, contextOfs));
        }
        return targets;
    }

    private static boolean isCanonicalROMAddress(int ofs) {
        return isCanonicalROMAddress(ofs, ofs);
    }

    private static boolean isCanonicalROMAddress(int ofs, int contextOfs) {
        // Output only labels in the project's canonical CPU range. For
        // NROM-128, emitting a label for a mirror operand would rewrite the
        // high byte and break parity.
        if (mapperNumber == MAPPER_MMC1) {
            return isStaticallyMappedCpuAddress(readCpuAddress(ofs), contextOfs);
        }
        return isCanonicalCpuAddress(readCpuAddress(ofs));
    }

    public static void checkDataLabel(int ofs) {
        checkDataLabel(ofs, ofs);
    }

    public static void checkDataLabel(int ofs, int contextOfs) {
        if (isROMAddress(ofs, contextOfs)) {
            int addr = getAddressForContext(ofs, contextOfs);
            if (!isCode(addr)) {
                for (int i=1; i<4; i++) {
                    if ((addr-i > 0) && isData(addr-i) && isLabel(addr-i)) {
                        return;
                    }
                    if ((addr+i < prgSize) && isData(addr+i) && isLabel(addr+i)) {
                        return;
                    }
                }
                map[addr] |= LABEL;
            }
        }
    }

/**
* Makes sure that every non-mapped (DATA) chunk is labelled in the disassembly.
**/

    public static void verifyDataLabels() {
        for (int i=1; i<prgSize; i++) {
            if (isCode(i-1) && isData(i)) {
                map[i] |= LABEL;
            }
        }
    }

/**
* Emits one resolved inline record in spec §9.1 form. Adjacent u8 and
* bytes(N) fields share a .DB line, each pointer field emits a single .DW
* expression that reproduces the original encoded word, and counted8 emits
* its count and payload as one logical .DB record (wrap may split it across
* multiple .DB lines but the count never gets a dedicated line). Records
* from separate callsites are never merged because the outer loop dispatches
* per record_start.
**/

    public static void emitInlineRecord(ResolvedRecord r) {
        // Label the record start.
        String startLabel = labelForOffset(r.recordStart);
        if (toHtml) {
            System.out.println("<A NAME=" + startLabel + "><BR>");
        }
        System.out.print(startLabel + ":");
        newLine();
        InlineField[] fields = r.layout.fields;
        int k = 0;
        while (k < fields.length) {
            InlineField f = fields[k];
            if (f.kind == InlineField.PTR16) {
                emitPointerField(r, k);
                k++;
            } else if (f.kind == InlineField.COUNTED8) {
                emitCountedField(r, k);
                k++;
            } else {
                // U8 or BYTES — collect adjacent run for one .DB sequence.
                int runEnd = k;
                while (runEnd < fields.length
                       && (fields[runEnd].kind == InlineField.U8
                           || fields[runEnd].kind == InlineField.BYTES)) {
                    runEnd++;
                }
                emitDataRunFields(r, k, runEnd);
                k = runEnd;
            }
        }
    }

    private static void emitDataRunFields(ResolvedRecord r, int kStart, int kEnd) {
        int start = r.fieldStarts[kStart];
        int end = r.fieldEnds[kEnd - 1];
        emitDbRun(start, end);
    }

    private static void emitCountedField(ResolvedRecord r, int k) {
        int start = r.fieldStarts[k];
        int end = r.fieldEnds[k];
        emitDbRun(start, end);
    }

    private static void emitDbRun(int start, int end) {
        System.out.print(".DB $" + hexLookup[ROM[start]]);
        int wrapCount = 1;
        for (int i = start + 1; i < end; i++) {
            if ((wrapCount++ & 15) == 0) {
                newLine();
                System.out.print(".DB ");
            } else {
                System.out.print(",");
            }
            System.out.print("$" + hexLookup[ROM[i]]);
        }
        newLine();
    }

    private static void emitPointerField(ResolvedRecord r, int k) {
        InlineField f = r.layout.fields[k];
        int target = r.pointerTargets[k];
        int adj = f.pointerAdjustment;
        String labelStr = labelForOffset(target);
        System.out.print(".DW ");
        printLabel(labelStr);
        if (adj > 0) {
            // adjusted target = encoded + adj ⇒ encoded = target - adj
            System.out.print("-" + adj);
        } else if (adj < 0) {
            System.out.print("+" + (-adj));
        }
        newLine();
    }

/**
* Phase-1 mask construction for configured data ranges. Blocks every byte
* in each range from being decoded as code. The parser already guarantees
* ranges don't overlap or touch each other, so no overlap check is needed
* here. Record-vs-range overlaps are caught by blockKnownInlineRecords
* when it runs after this method.
**/

    public static void blockDataRanges() {
        for (int k = 0; k < dataRanges.entries.length; k++) {
            DataRangeEntry r = dataRanges.entries[k];
            for (int i = r.start; i < r.end; i++) {
                blockedFromCode[i] = true;
            }
        }
    }

/**
* Phase-2 label + seed for configured data ranges. Labels each range start
* and labels + seeds the exclusive end as a code continuation when the end
* is still inside ROM. Must run only after blockDataRanges and
* blockKnownInlineRecords have populated the complete barrier mask.
**/

    public static void labelAndSeedDataRanges() {
        for (int k = 0; k < dataRanges.entries.length; k++) {
            DataRangeEntry r = dataRanges.entries[k];
            map[r.start] |= LABEL;
            if (r.end < prgSize) {
                if (blockedFromCode[r.end]) {
                    failBlockedConflict(r.end, "data range continuation after $"
                        + hex4(r.startCpu) + "+" + r.length);
                }
                map[r.end] |= LABEL;
                processCode(r.end);
            }
        }
    }

/**
* Convenience composite used by single-range tests. Runs block + label/seed
* back-to-back; runAnalysisPass uses the split phase methods directly so all
* barriers are constructed before any seed traces.
**/

    public static void applyDataRangeBarriers() {
        blockDataRanges();
        labelAndSeedDataRanges();
    }

/**
*
**/

    public static boolean needsWideningSuffixForZeroPageAddresses(int op) {
        switch (op) {
            case 0x6D:  return true;    /* ADC oper */
            case 0x7D:  return true;    /* ADC oper,X */
            case 0x2D:  return true;    /* AND oper */
            case 0x3D:  return true;    /* AND oper,X */
            case 0x0E:  return true;    /* ASL oper */
            case 0x1E:  return true;    /* ASL oper,X */
            case 0x2C:  return true;    /* BIT oper */
            case 0xCD:  return true;    /* CMP oper */
            case 0xDD:  return true;    /* CMP oper,X */
            case 0xEC:  return true;    /* CPX oper */
            case 0xCC:  return true;    /* CPY oper */
            case 0xCE:  return true;    /* DEC oper */
            case 0xDE:  return true;    /* DEC oper,X */
            case 0x4D:  return true;    /* EOR oper */
            case 0x5D:  return true;    /* EOR oper,X */
            case 0xEE:  return true;    /* INC oper */
            case 0xFE:  return true;    /* INC oper,X */
            case 0xAD:  return true;    /* LDA oper */
            case 0xBD:  return true;    /* LDA oper,X */
            case 0xAE:  return true;    /* LDX oper */
            case 0xBE:  return true;    /* LDX oper,Y */
            case 0xAC:  return true;    /* LDY oper */
            case 0xBC:  return true;    /* LDY oper,X */
            case 0x4E:  return true;    /* LSR oper */
            case 0x5E:  return true;    /* LSR oper,X */
            case 0x0D:  return true;    /* ORA oper */
            case 0x1D:  return true;    /* ORA oper,X */
            case 0x2E:  return true;    /* ROL oper */
            case 0x3E:  return true;    /* ROL oper,X */
            case 0x6E:  return true;    /* ROR oper */
            case 0x7E:  return true;    /* ROR oper,X */
            case 0xED:  return true;    /* SBC oper */
            case 0xFD:  return true;    /* SBC oper,X */
            case 0x8D:  return true;    /* STA oper */
            case 0x9D:  return true;    /* STA oper,X */
            case 0x8E:  return true;    /* STX oper */
            case 0x8C:  return true;    /* STY oper */
        }
        return false;
    }

    public static void printAddress(int ofs, int op) {
        printAddress(ofs, op, ofs);
    }

    public static void printAddress(int ofs, int op, int contextOfs) {
        String label=null;
        if (isCanonicalROMAddress(ofs, contextOfs)) {   // safe canonical ROM operand
            System.out.print(" ");
            int a = getAddressForContext(ofs, contextOfs);
            if (!isLabel(a)) {  // no label exists for this address!
                for (int i=1; i<16; i++) {
                    if (isLabel(a-i)) { // no problem, use label of address-i
                        a-=i;
                        printLabel(labelForOffset(a));
                        System.out.print("+"+i);
                        return;
                    }
                    else if (isLabel(a+i)) {    // no problem, use label of address+i
                        a+=i;
                        printLabel(labelForOffset(a));
                        System.out.print("-"+i);
                        return;
                    }
                }
                // whoops, no label found, need to print hardcoded address...
                System.out.print("$"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
            }
            else {
                printLabel(labelForOffset(a));
            }
        }
        else {  // print address as direct memory offset ($XXXX)
	    if ((ROM[ofs+1] == 0) && needsWideningSuffixForZeroPageAddresses(op))
                System.out.print(".W");
            System.out.print(" ");
            System.out.print("$"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
        }
    }

    private static void printRelativeLiteral(int ofs) {
        int dist = ROM[ofs+1];
        if (dist < 0x80) {
            int addr = ofs + 2 + dist;
            System.out.print("$+" + (addr - ofs));
        }
        else {
            dist = (dist ^ 0xFF) + 1;
            int addr = ofs + 2 - dist;
            System.out.print("$-" + (ofs - 2 - addr));
        }
    }

/**
*
**/

    public static void printLabel(String label) {
        if (toHtml)
            System.out.print("<A HREF=\"#"+label+"\">");
        System.out.print(label);
        if (toHtml)
            System.out.print("</A>");
    }

/**
*
**/

    public static boolean isCode(int ofs) {
        if (!inPrgOffset(ofs))
            return false;
        else
            return ((map[ofs] & CODE) != 0);
    }

/**
*
**/

    public static boolean isData(int ofs) {
        if (!inPrgOffset(ofs))
            return false;
        else
            return ((map[ofs] & DATA) != 0);
    }

/**
*
**/

    public static boolean isLabel(int ofs) {
        if (!inPrgOffset(ofs))
            return false;
        else
            return ((map[ofs] & LABEL) != 0);
    }

/**
*
**/

    public static boolean isPtr(int ofs) {
        if (!inPrgOffset(ofs))
            return false;
        else
            return ((map[ofs] & PTR) != 0);
    }

/**
*
**/

    public static boolean isInstr(int ofs) {
        if (!inPrgOffset(ofs))
            return false;
        else
            return ((map[ofs] & INSTR) != 0);
    }

/**
*
**/

    public static void newLine() {
        if (toHtml)
            System.out.println("<BR>");
        else
            System.out.println("");
    }

/**
* A configured inline record after a JSR callsite has been validated against
* the ROM. Carries per-field start/end offsets and adjusted pointer targets
* so the analysis and output passes don't have to re-walk the layout against
* raw bytes.
**/

    public static final class ResolvedRecord {
        public final int callsite;          // PRG offset of the JSR opcode
        public final InlineCallEntry entry; // schema this record was resolved against
        public final int recordStart;       // callsite + 3
        public final int recordEnd;         // exclusive PRG offset
        public final int[] fieldStarts;     // per-field start offset, parallel to entry.layout.fields
        public final int[] fieldEnds;       // per-field exclusive end offset
        public final int[] pointerTargets;  // adjusted target as PRG offset; -1 for non-pointer fields

        public final InlineLayout layout;   // alias of entry.layout for convenience

        ResolvedRecord(int callsite, InlineCallEntry entry, int recordStart, int recordEnd,
                       int[] fieldStarts, int[] fieldEnds, int[] pointerTargets) {
            this.callsite = callsite;
            this.entry = entry;
            this.layout = entry.layout;
            this.recordStart = recordStart;
            this.recordEnd = recordEnd;
            this.fieldStarts = fieldStarts;
            this.fieldEnds = fieldEnds;
            this.pointerTargets = pointerTargets;
        }
    }

/**
* Thrown by configuration parsers for malformed input. Main translates these
* to a one-line error via exitWithError; tests can catch and inspect.
**/

    public static class ConfigException extends RuntimeException {
        public ConfigException(String message) {
            super(message);
        }
    }

/**
* Pointer-kind enum for ptr16 fields. Code targets are seeded to the code
* worklist; data targets are labeled at the unclassified DATA state and may
* still become code if reached independently through valid control flow.
**/

    public static final class PointerKind {
        public static final int CODE = 0;
        public static final int DATA = 1;
        private PointerKind() {}
    }

/**
* One field of an inline-record layout. Immutable; constructed only by the
* parser via the static factory methods.
**/

    public static final class InlineField {
        public static final int U8       = 0;
        public static final int BYTES    = 1;
        public static final int COUNTED8 = 2;
        public static final int PTR16    = 3;

        public final int kind;
        // Fixed byte count for this field; for COUNTED8 this is just the count
        // byte (1) — the variable payload size is resolved at apply time from
        // the value of that byte.
        public final int byteCount;
        // PointerKind.CODE or PointerKind.DATA when kind == PTR16; -1 otherwise.
        public final int pointerKind;
        // Signed adjustment for PTR16; 0 for non-pointer fields.
        public final int pointerAdjustment;

        private InlineField(int kind, int byteCount, int pointerKind, int pointerAdjustment) {
            this.kind = kind;
            this.byteCount = byteCount;
            this.pointerKind = pointerKind;
            this.pointerAdjustment = pointerAdjustment;
        }

        public static InlineField u8() {
            return new InlineField(U8, 1, -1, 0);
        }
        public static InlineField bytes(int n) {
            return new InlineField(BYTES, n, -1, 0);
        }
        public static InlineField counted8() {
            return new InlineField(COUNTED8, 1, -1, 0);
        }
        public static InlineField ptr16(int pointerKind, int adjustment) {
            return new InlineField(PTR16, 2, pointerKind, adjustment);
        }

        public boolean isPointer() {
            return kind == PTR16;
        }
        public boolean isVariable() {
            return kind == COUNTED8;
        }
    }

/**
* Layout for one configured callee. Immutable; field array is shared by
* reference but never mutated after construction.
**/

    public static final class InlineLayout {
        public final InlineField[] fields;
        // Sum of byteCount over all fields. For variable layouts this is the
        // fixed prefix; the COUNTED8 count byte contributes 1 here and its
        // payload size is added at apply time.
        public final int fixedSize;
        public final boolean hasCounted8;

        InlineLayout(InlineField[] fields) {
            this.fields = fields;
            int sum = 0;
            boolean variable = false;
            for (int i = 0; i < fields.length; i++) {
                sum += fields[i].byteCount;
                if (fields[i].kind == InlineField.COUNTED8) {
                    variable = true;
                }
            }
            this.fixedSize = sum;
            this.hasCounted8 = variable;
        }
    }

/**
* One row from inlinecalls.csv.
**/

    public static final class InlineCallEntry {
        public static final int ANY_CALLSITE = -1;

        // PRG offset of the exact JSR opcode for callsite-specific rows, or
        // ANY_CALLSITE for legacy per-callee rows.
        public final int callsite;
        // Canonical project CPU address for diagnostics, or -1 for legacy rows.
        public final int callsiteCpu;
        // PRG offset, used for callsite lookups against
        // getAddress() results from the JSR operand.
        public final int callee;
        // Canonical project CPU address, kept for diagnostics.
        public final int calleeCpu;
        public final InlineLayout layout;
        public final int sourceLine;

        InlineCallEntry(int callee, int calleeCpu, InlineLayout layout, int sourceLine) {
            this(ANY_CALLSITE, -1, callee, calleeCpu, layout, sourceLine);
        }

        InlineCallEntry(int callsite, int callsiteCpu, int callee, int calleeCpu,
            InlineLayout layout, int sourceLine) {
            this.callsite = callsite;
            this.callsiteCpu = callsiteCpu;
            this.callee = callee;
            this.calleeCpu = calleeCpu;
            this.layout = layout;
            this.sourceLine = sourceLine;
        }
    }

/**
* Parsed inlinecalls.csv. Lookup is by PRG-offset callee; CPU addresses are
* preserved on each entry for diagnostics.
**/

    public static final class InlineCallsConfig {
        public static final InlineCallsConfig EMPTY = new InlineCallsConfig(new InlineCallEntry[0]);

        public final InlineCallEntry[] entries;
        private final HashMap<Integer, InlineCallEntry> byCallee;
        private final HashMap<Integer, InlineCallEntry> byCallsite;

        InlineCallsConfig(InlineCallEntry[] entries) {
            this.entries = entries;
            this.byCallee = new HashMap<Integer, InlineCallEntry>();
            this.byCallsite = new HashMap<Integer, InlineCallEntry>();
            for (int i = 0; i < entries.length; i++) {
                if (entries[i].callsite == InlineCallEntry.ANY_CALLSITE) {
                    byCallee.put(entries[i].callee, entries[i]);
                } else {
                    byCallsite.put(entries[i].callsite, entries[i]);
                }
            }
        }

        public InlineCallEntry findByCallee(int prgOffset) {
            return byCallee.get(prgOffset);
        }

        public InlineCallEntry findForCallsite(int callsitePrgOffset, int calleePrgOffset) {
            InlineCallEntry entry = byCallsite.get(callsitePrgOffset);
            if (entry != null) {
                if (entry.callee != calleePrgOffset) {
                    throw new ConfigException("inlinecalls: callsite $" + cpuLabel(callsitePrgOffset)
                        + " configured for callee $" + hex4(entry.calleeCpu)
                        + " but JSR targets $" + cpuLabel(calleePrgOffset));
                }
                return entry;
            }
            return byCallee.get(calleePrgOffset);
        }

        public boolean isEmpty() {
            return entries.length == 0;
        }

        private enum InlineCallsHeader {
            CALLEE,
            BANK_CALLEE,
            CALLSITE,
            BANK_CALLSITE
        }

        public static InlineCallsConfig parse(String path) {
            File f = new File(path);
            if (!f.canRead()) {
                throw new ConfigException("inlinecalls: couldn't read " + path);
            }
            ArrayList<InlineCallEntry> rows = new ArrayList<InlineCallEntry>();
            HashSet<Integer> seenCallees = new HashSet<Integer>();
            HashSet<Integer> seenCallsites = new HashSet<Integer>();
            boolean headerSeen = false;
            InlineCallsHeader header = null;
            int lineNo = 0;
            try (BufferedReader br = new BufferedReader(new FileReader(f))) {
                String raw;
                while ((raw = br.readLine()) != null) {
                    lineNo++;
                    String line = stripConfigComments(raw).trim();
                    if (line.length() == 0) {
                        continue;
                    }
                    if (!headerSeen) {
                        if (line.equals("callee|layout")) {
                            header = InlineCallsHeader.CALLEE;
                        } else if (line.equals("bank|callee|layout")) {
                            header = InlineCallsHeader.BANK_CALLEE;
                        } else if (line.equals("callsite|callee|layout")) {
                            header = InlineCallsHeader.CALLSITE;
                        } else if (line.equals("bank|callsite|callee|layout")) {
                            header = InlineCallsHeader.BANK_CALLSITE;
                        } else {
                            throw new ConfigException("inlinecalls: expected header 'callee|layout', "
                                + "'bank|callee|layout', 'callsite|callee|layout', or "
                                + "'bank|callsite|callee|layout' at line " + lineNo
                                + ", got '" + line + "'");
                        }
                        headerSeen = true;
                        continue;
                    }
                    String[] parts = line.split("\\|", -1);
                    if (parts.length == 1) {
                        throw new ConfigException("inlinecalls: missing '|' at line " + lineNo + ": " + line);
                    }
                    int expectedParts = (header == InlineCallsHeader.CALLEE) ? 2
                        : (header == InlineCallsHeader.BANK_CALLSITE) ? 4
                        : 3;
                    if (parts.length != expectedParts) {
                        throw new ConfigException("inlinecalls: bad row at line " + lineNo + ": " + line);
                    }
                    String callsiteStr = "";
                    String calleeStr = "";
                    String layoutStr = "";
                    int callsite = InlineCallEntry.ANY_CALLSITE;
                    int callsiteCpu = -1;
                    int callee;
                    int calleeCpu;
                    if (header == InlineCallsHeader.CALLEE) {
                        calleeStr = parts[0].trim();
                        layoutStr = parts[1].trim();
                    } else if (header == InlineCallsHeader.BANK_CALLEE) {
                        calleeStr = parts[1].trim();
                        layoutStr = parts[2].trim();
                    } else if (header == InlineCallsHeader.CALLSITE) {
                        callsiteStr = parts[0].trim();
                        calleeStr = parts[1].trim();
                        layoutStr = parts[2].trim();
                    } else {
                        callsiteStr = parts[1].trim();
                        calleeStr = parts[2].trim();
                        layoutStr = parts[3].trim();
                    }
                    if (callsiteStr.length() == 0
                        && (header == InlineCallsHeader.CALLSITE
                            || header == InlineCallsHeader.BANK_CALLSITE)) {
                        throw new ConfigException("inlinecalls: empty callsite at line " + lineNo);
                    }
                    if (calleeStr.length() == 0) {
                        throw new ConfigException("inlinecalls: empty callee at line " + lineNo);
                    }
                    if (layoutStr.length() == 0) {
                        throw new ConfigException("inlinecalls: empty layout at line " + lineNo);
                    }
                    if (header == InlineCallsHeader.CALLEE) {
                        calleeCpu = parseRawCpuAddress("inlinecalls", calleeStr, lineNo);
                        callee = cpuToPrgOffset(parseCpuAddress("inlinecalls", calleeStr, lineNo));
                    } else if (header == InlineCallsHeader.BANK_CALLEE) {
                        calleeCpu = parseRawCpuAddress("inlinecalls", calleeStr, lineNo);
                        callee = parseBankedPrgOffset("inlinecalls", parts[0].trim(), calleeStr, lineNo);
                    } else if (header == InlineCallsHeader.CALLSITE) {
                        callsiteCpu = parseRawCpuAddress("inlinecalls", callsiteStr, lineNo);
                        callsite = cpuToPrgOffset(parseCpuAddress("inlinecalls", callsiteStr, lineNo));
                        calleeCpu = parseRawCpuAddress("inlinecalls", calleeStr, lineNo);
                        callee = parseInlineCallsiteCallee(calleeStr, calleeCpu, callsite, lineNo);
                    } else {
                        callsiteCpu = parseRawCpuAddress("inlinecalls", callsiteStr, lineNo);
                        callsite = parseBankedPrgOffset("inlinecalls", parts[0].trim(), callsiteStr, lineNo);
                        calleeCpu = parseRawCpuAddress("inlinecalls", calleeStr, lineNo);
                        callee = parseInlineCallsiteCallee(calleeStr, calleeCpu, callsite, lineNo);
                    }
                    if (callsite == InlineCallEntry.ANY_CALLSITE) {
                        if (!seenCallees.add(callee)) {
                            throw new ConfigException("inlinecalls: duplicate callee $" + hex4(calleeCpu)
                                + " at line " + lineNo);
                        }
                    } else if (!seenCallsites.add(callsite)) {
                        throw new ConfigException("inlinecalls: duplicate callsite $" + hex4(callsiteCpu)
                            + " at line " + lineNo);
                    }
                    InlineLayout layout = parseInlineLayout(layoutStr, lineNo);
                    rows.add(new InlineCallEntry(callsite, callsiteCpu, callee, calleeCpu,
                        layout, lineNo));
                }
            } catch (IOException ex) {
                throw new ConfigException("inlinecalls: I/O error reading " + path + ": " + ex.getMessage());
            }
            if (!headerSeen) {
                throw new ConfigException("inlinecalls: missing header in " + path);
            }
            return new InlineCallsConfig(rows.toArray(new InlineCallEntry[0]));
        }

        private static int parseInlineCallsiteCallee(String calleeStr, int calleeCpu,
            int callsite, int lineNo) {
            if (isCpuRomAddress(calleeCpu)) {
                return cpuToPrgOffsetForContext(calleeCpu, callsite);
            }
            throw new ConfigException("inlinecalls: CPU address out of "
                + cpuRangeLabel() + " range at line " + lineNo
                + ": $" + hex4(calleeCpu));
        }
    }

/**
* One row from dataranges.csv. `end` is exclusive (start + length).
**/

    public static final class DataRangeEntry {
        public final int start;        // PRG offset
        public final int startCpu;     // canonical project CPU address
        public final int length;
        public final int end;          // exclusive PRG offset
        public final int sourceLine;

        DataRangeEntry(int start, int startCpu, int length, int sourceLine) {
            this.start = start;
            this.startCpu = startCpu;
            this.length = length;
            this.end = start + length;
            this.sourceLine = sourceLine;
        }
    }

/**
* Parsed dataranges.csv. Entries are sorted by start; adjacent or overlapping
* ranges are rejected at parse time.
**/

    public static final class DataRangesConfig {
        public static final DataRangesConfig EMPTY = new DataRangesConfig(new DataRangeEntry[0]);

        public final DataRangeEntry[] entries;

        DataRangesConfig(DataRangeEntry[] entries) {
            this.entries = entries;
        }

        public boolean isEmpty() {
            return entries.length == 0;
        }

        public static DataRangesConfig parse(String path) {
            File f = new File(path);
            if (!f.canRead()) {
                throw new ConfigException("dataranges: couldn't read " + path);
            }
            ArrayList<DataRangeEntry> rows = new ArrayList<DataRangeEntry>();
            boolean headerSeen = false;
            int lineNo = 0;
            try (BufferedReader br = new BufferedReader(new FileReader(f))) {
                String raw;
                while ((raw = br.readLine()) != null) {
                    lineNo++;
                    String line = stripConfigComments(raw).trim();
                    if (line.length() == 0) {
                        continue;
                    }
                    if (!headerSeen) {
                        if (!line.equals("start|length") && !line.equals("bank|addr|length")) {
                            throw new ConfigException("dataranges: expected header 'start|length' or "
                                + "'bank|addr|length' at line " + lineNo + ", got '" + line + "'");
                        }
                        headerSeen = true;
                        continue;
                    }
                    String[] parts = line.split("\\|", -1);
                    if (parts.length == 1) {
                        throw new ConfigException("dataranges: missing '|' at line " + lineNo + ": " + line);
                    }
                    if (parts.length != 2 && parts.length != 3) {
                        throw new ConfigException("dataranges: bad row at line " + lineNo + ": " + line);
                    }
                    String startStr = parts.length == 2 ? parts[0].trim() : parts[1].trim();
                    String lenStr = parts.length == 2 ? parts[1].trim() : parts[2].trim();
                    if (startStr.length() == 0) {
                        throw new ConfigException("dataranges: empty start at line " + lineNo);
                    }
                    if (lenStr.length() == 0) {
                        throw new ConfigException("dataranges: empty length at line " + lineNo);
                    }
                    int startCpu = parseRawCpuAddress("dataranges", startStr, lineNo);
                    int length;
                    try {
                        length = Integer.parseInt(lenStr);
                    } catch (NumberFormatException ex) {
                        throw new ConfigException("dataranges: length must be a positive decimal integer at line "
                            + lineNo + ": " + lenStr);
                    }
                    if (length <= 0) {
                        throw new ConfigException("dataranges: length must be > 0 at line " + lineNo + ": " + lenStr);
                    }
                    int start = parts.length == 2
                        ? cpuToPrgOffset(parseCpuAddress("dataranges", startStr, lineNo))
                        : parseBankedPrgOffset("dataranges", parts[0].trim(), startStr, lineNo);
                    long endLong = (long) start + (long) length;
                    if (endLong > (long) prgSize) {
                        throw new ConfigException("dataranges: range $" + hex4(startCpu) + "+" + length
                            + " exceeds ROM at line " + lineNo);
                    }
                    rows.add(new DataRangeEntry(start, startCpu, length, lineNo));
                }
            } catch (IOException ex) {
                throw new ConfigException("dataranges: I/O error reading " + path + ": " + ex.getMessage());
            }
            if (!headerSeen) {
                throw new ConfigException("dataranges: missing header in " + path);
            }
            DataRangeEntry[] arr = rows.toArray(new DataRangeEntry[0]);
            Arrays.sort(arr, new Comparator<DataRangeEntry>() {
                public int compare(DataRangeEntry a, DataRangeEntry b) {
                    return Integer.compare(a.start, b.start);
                }
            });
            for (int i = 1; i < arr.length; i++) {
                DataRangeEntry prev = arr[i-1];
                DataRangeEntry cur = arr[i];
                if (cur.start < prev.end) {
                    throw new ConfigException("dataranges: ranges $" + hex4(prev.startCpu) + "+" + prev.length
                        + " (line " + prev.sourceLine + ") and $" + hex4(cur.startCpu) + "+" + cur.length
                        + " (line " + cur.sourceLine + ") overlap");
                }
                if (cur.start == prev.end) {
                    throw new ConfigException("dataranges: ranges $" + hex4(prev.startCpu) + "+" + prev.length
                        + " (line " + prev.sourceLine + ") and $" + hex4(cur.startCpu) + "+" + cur.length
                        + " (line " + cur.sourceLine + ") touch; merge them");
                }
            }
            return new DataRangesConfig(arr);
        }
    }

/**
* Shared parser helpers.
**/

    private static String stripConfigComments(String line) {
        int hashAt = line.indexOf('#');
        if (hashAt >= 0) {
            line = line.substring(0, hashAt);
        }
        int semiAt = line.indexOf(';');
        if (semiAt >= 0) {
            line = line.substring(0, semiAt);
        }
        return line;
    }

    private static int parseCpuAddress(String fileLabel, String token, int lineNo) {
        int v = parseRawCpuAddress(fileLabel, token, lineNo);
        if (!isCanonicalCpuAddress(v)) {
            throw new ConfigException(fileLabel + ": CPU address out of "
                + cpuRangeLabel() + " range at line " + lineNo
                + ": $" + hex4(v));
        }
        return v;
    }

    private static int parseRawCpuAddress(String fileLabel, String token, int lineNo) {
        String t = token.trim();
        if (t.startsWith("$")) {
            t = t.substring(1);
        } else if (t.startsWith("0x") || t.startsWith("0X")) {
            t = t.substring(2);
        }
        if (t.length() == 0) {
            throw new ConfigException(fileLabel + ": empty address at line " + lineNo + ": " + token);
        }
        int v;
        try {
            v = Integer.parseInt(t, 16);
        } catch (NumberFormatException ex) {
            throw new ConfigException(fileLabel + ": bad CPU address at line " + lineNo + ": " + token);
        }
        return v;
    }

    private static String hex4(int v) {
        String s = Integer.toHexString(v & 0xFFFF).toUpperCase();
        while (s.length() < 4) {
            s = "0" + s;
        }
        return s;
    }

/**
* Layout grammar:
*   layout       := field ("," field)*
*   field        := "u8"
*                 | "bytes(" positive_integer ")"
*                 | "counted8"
*                 | "ptr16(" pointer_kind ["," signed_integer] ")"
*   pointer_kind := "code" | "data"
* counted8 must be the final field. Whitespace around fields and inside
* parenthesised arguments is ignored.
**/

    static InlineLayout parseInlineLayout(String spec, int lineNo) {
        ArrayList<InlineField> fields = new ArrayList<InlineField>();
        int i = 0;
        int n = spec.length();
        while (i < n) {
            while (i < n && Character.isWhitespace(spec.charAt(i))) {
                i++;
            }
            if (i >= n) {
                throw new ConfigException("inlinecalls: trailing ',' in layout at line " + lineNo + ": " + spec);
            }
            int tokStart = i;
            while (i < n && (Character.isLetterOrDigit(spec.charAt(i)) || spec.charAt(i) == '_')) {
                i++;
            }
            String tok = spec.substring(tokStart, i);
            if (tok.length() == 0) {
                throw new ConfigException("inlinecalls: unexpected character '" + spec.charAt(i)
                    + "' in layout at line " + lineNo + ": " + spec);
            }
            if (tok.equals("u8")) {
                fields.add(InlineField.u8());
            } else if (tok.equals("counted8")) {
                fields.add(InlineField.counted8());
            } else if (tok.equals("bytes")) {
                while (i < n && Character.isWhitespace(spec.charAt(i))) {
                    i++;
                }
                if (i >= n || spec.charAt(i) != '(') {
                    throw new ConfigException("inlinecalls: 'bytes' must be followed by '(' at line " + lineNo);
                }
                int close = spec.indexOf(')', i);
                if (close < 0) {
                    throw new ConfigException("inlinecalls: 'bytes(...)' missing ')' at line " + lineNo);
                }
                String inner = spec.substring(i + 1, close).trim();
                int count;
                try {
                    count = Integer.parseInt(inner);
                } catch (NumberFormatException ex) {
                    throw new ConfigException("inlinecalls: 'bytes(N)' expects a positive integer at line "
                        + lineNo + ": '" + inner + "'");
                }
                if (count <= 0) {
                    throw new ConfigException("inlinecalls: 'bytes(N)' requires N > 0 at line " + lineNo
                        + ": " + count);
                }
                fields.add(InlineField.bytes(count));
                i = close + 1;
            } else if (tok.equals("ptr16")) {
                while (i < n && Character.isWhitespace(spec.charAt(i))) {
                    i++;
                }
                if (i >= n || spec.charAt(i) != '(') {
                    throw new ConfigException("inlinecalls: 'ptr16' must be followed by '(' at line " + lineNo);
                }
                int close = spec.indexOf(')', i);
                if (close < 0) {
                    throw new ConfigException("inlinecalls: 'ptr16(...)' missing ')' at line " + lineNo);
                }
                String inner = spec.substring(i + 1, close);
                String[] parts = inner.split(",", -1);
                if (parts.length < 1 || parts.length > 2) {
                    throw new ConfigException("inlinecalls: 'ptr16' expects 1 or 2 arguments at line " + lineNo
                        + ": '" + inner + "'");
                }
                String kindStr = parts[0].trim();
                int pointerKind;
                if (kindStr.equals("code")) {
                    pointerKind = PointerKind.CODE;
                } else if (kindStr.equals("data")) {
                    pointerKind = PointerKind.DATA;
                } else {
                    throw new ConfigException("inlinecalls: 'ptr16' kind must be 'code' or 'data' at line "
                        + lineNo + ": '" + kindStr + "'");
                }
                int adj = 0;
                if (parts.length == 2) {
                    String adjStr = parts[1].trim();
                    if (adjStr.length() == 0) {
                        throw new ConfigException("inlinecalls: 'ptr16' adjustment is empty at line " + lineNo);
                    }
                    try {
                        adj = Integer.parseInt(adjStr);
                    } catch (NumberFormatException ex) {
                        throw new ConfigException("inlinecalls: 'ptr16' adjustment must be a signed integer at line "
                            + lineNo + ": '" + adjStr + "'");
                    }
                }
                fields.add(InlineField.ptr16(pointerKind, adj));
                i = close + 1;
            } else {
                throw new ConfigException("inlinecalls: unknown field '" + tok + "' at line " + lineNo);
            }
            while (i < n && Character.isWhitespace(spec.charAt(i))) {
                i++;
            }
            if (i < n) {
                if (spec.charAt(i) != ',') {
                    throw new ConfigException("inlinecalls: expected ',' between fields at line " + lineNo
                        + " near offset " + i + ": " + spec);
                }
                i++;
                // A comma must be followed by another field; trailing ',' is an error.
                int j = i;
                while (j < n && Character.isWhitespace(spec.charAt(j))) {
                    j++;
                }
                if (j >= n) {
                    throw new ConfigException("inlinecalls: trailing ',' in layout at line " + lineNo + ": " + spec);
                }
            }
        }
        if (fields.size() == 0) {
            throw new ConfigException("inlinecalls: empty layout at line " + lineNo);
        }
        InlineField[] arr = fields.toArray(new InlineField[0]);
        for (int k = 0; k < arr.length; k++) {
            if (arr[k].kind == InlineField.COUNTED8 && k != arr.length - 1) {
                throw new ConfigException("inlinecalls: 'counted8' must be the final field at line " + lineNo);
            }
        }
        return new InlineLayout(arr);
    }

}   // bye.
