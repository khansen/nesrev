import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.util.ArrayDeque;
import java.util.ArrayList;

/**
 * NESrev - A disassembler for 16K NES PRG-ROMs
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
    // the status map
    private static int[] map;
    // the name of the ROM, extracted from the cmdline arg
    private static String name;
    // is set to true if HTML output is desired
    private static boolean toHtml=false;
    // iterative code target worklist used by processCode()
    private static ArrayDeque<Integer> codeWorklist = new ArrayDeque<Integer>();
    private static boolean processCodeActive = false;
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
        System.out.println("Syntax: java NESrev [ROMfile] <-html> <-codepointers FILE>");
    }

    private static void exitWithError(String message) {
        System.err.println(message);
        System.exit(1);
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
        if (f.length() != 0x4000) {
            exitWithError("Error: ROM must be 16,384 bytes in size.");
        }
        name = f.getName();

        ArrayList<Integer> codePointersStart = new ArrayList<Integer>();
        ArrayList<Integer> codePointersCount = new ArrayList<Integer>();
        // parse rest of arguments
        for (int i=1; i<args.length; i++) {
            if (args[i].equals("-html")) {
                toHtml = true;
            }
            else if (args[i].equals("-codepointers")) {
                if (i + 1 >= args.length) {
                    exitWithError("Error: Missing filename after -codepointers.");
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
                        line = line.trim();
                        if (line.length() == 0 || line.startsWith("#")) {
                            continue;
                        }
                        if (lineNo == 1 && line.equalsIgnoreCase("start|count")) {
                            continue;
                        }
                        String[] parts = line.split("\\|", -1);
                        if (parts.length != 2) {
                            exitWithError("Error: Bad code pointer config format at line " + lineNo + ": " + line);
                        }
                        int offset;
                        int count;
                        try {
                            offset = Integer.decode(parts[0].trim());
                            count = Integer.decode(parts[1].trim());
                        } catch (NumberFormatException ex) {
                            exitWithError("Error: Bad numeric value at line " + lineNo + ": " + line);
                            return;
                        }
                        long pointerTableEnd = (long) offset + ((long) count * 2L);
                        if (offset < 0 || count < 0 || pointerTableEnd > 0x4000L) {
                            exitWithError("Error: Code pointer addresses are out of range at line " + lineNo + ".");
                        }
                        codePointersStart.add(offset);
                        codePointersCount.add(count);
                    }
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

        // init map
        map = new int[ROM.length];
        for (int i=0; i<map.length; i++) {
            map[i] = DATA;
        }

        // add the fixed vectors
	codePointersStart.add(0x3FFA);
        codePointersCount.add(3);

        // mark the code pointers
	for (int i = 0; i < codePointersStart.size(); ++i) {
            int offset = (int)codePointersStart.get(i);
            int count = (int)codePointersCount.get(i);
            for (int j = 0; j < count; ++j) {
                map[offset+j*2+0] = CODE | PTR;
                map[offset+j*2+1] = CODE | PTR;
            }
	}

	// process code pointers recursively
        for (int i = 0; i < codePointersStart.size(); ++i) {
            int offset = (int)codePointersStart.get(i);
            int count = (int)codePointersCount.get(i);
            for (int j = 0; j < count; ++j) {
                processCode(getAddress(offset+j*2));
            }
	}
        //
        verifyDataLabels();
        disassemble();
        //
        System.exit(0);
    }

/**
* Returns 14-bit address made up by the two bytes at offset ofs in the ROM.
**/

    public static int getAddress(int ofs) {
        return ((ROM[ofs+1]<<8) + ROM[ofs]) & 0x3FFF;
    }

/**
* Recursive function that maps out the code in the ROM.
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
        codeWorklist.addLast(ofs);
    }

    private static void queueRelativeBranchTarget(int ofs) {
        int dist = ROM[ofs+1];
        if (dist < 0x80) {  // branch forward
            queueCodeTarget(ofs+2+dist);
        }
        else {  // branch backward
            dist = (dist ^ 0xFF) + 1;
            queueCodeTarget(ofs+2-dist);
        }
    }

    private static boolean processCodeSingle(int ofs) {
        if (isCode(ofs) && !isInstr(ofs)) {
            return false;
        }
        boolean done=false, jsrchk=false;
        int op, len;
        int chkpt=ofs;  // initialize checkpoint to current offset
        int startofs=ofs;
        while (!done && isData(ofs)) {
            // process one opcode
            op = ROM[ofs];
            len = oplengthLookup[op];
            if (len > 0) {
                if ((ofs + len) > map.length) {
                    return false;
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
                    while ((ofs + 1 < map.length) && (map[ofs] == DATA) && (ROM[ofs+1] >= 0xC0)) {
                        queueCodeTarget(getAddress(ofs));
                        map[ofs++] = CODE | PTR;
                        map[ofs++] = CODE | PTR;
                    }
                }
                done = true;
            }

            if (!done && CHECK_DATA_LABEL_OPCODE[op]) {
                checkDataLabel(ofs+1);
            }

            if (!done && RELATIVE_BRANCH_OPCODE[op]) {
                queueRelativeBranchTarget(ofs);
                chkpt = ofs+2;
                jsrchk = false;
                ofs += len;
                continue;
            }

            switch (op) {
                case 0x20:  // JSR
                    queueCodeTarget(getAddress(ofs+1));
                    chkpt = ofs+3;
                    jsrchk = true;
                    break;

                case 0x40:  // RTI
                case 0x60:  // RTS
                    done = true;
                    break;

                case 0x4C:  // JMP Abs
                    queueCodeTarget(getAddress(ofs+1));
                    done = true;
                    break;

                case 0x6C:  // JMP Ind
                    if (isROMAddress(ofs+1)) {
                        queueCodeTarget(getAddress(getAddress(ofs+1)));
                    }
                    done = true;
                    break;

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
        System.out.print(".ORG $C000");
        newLine();
        newLine();
        //
        int ofs = 0, op, amode;
        while (ofs < 0x4000) {
            if (isCode(ofs)) {
                if (isPtr(ofs)) {   // print jump table
                    newLine();
                    while ((ofs < 0x4000) && isPtr(ofs)) {
                        System.out.print(".DW ");
                        if (isLabel(getAddress(ofs))) {
                            printLabel("L"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
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
                        String label = "L"+hexLookup[(ofs>>8)+0xC0]+hexLookup[ofs&0xFF];
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
                        printAddress(ofs+1, op);
                        newLine();
                    }
                    else if (amode == ABSX) {
                        printAddress(ofs+1, op);
                        System.out.print(",X");
                        newLine();
                    }
                    else if (amode == ABSY) {
                        printAddress(ofs+1, op);
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
                        int dist = ROM[ofs+1];
                        if (dist < 0x80) {
                            int addr = ofs+2+dist;
                            if (isLabel(addr)) {
                                printLabel("L"+hexLookup[(addr>>8)+0xC0]+hexLookup[addr&0xFF]);
                            }
                            else {
                                System.out.print("$+"+(addr-ofs));
                            }
                        }
                        else {
                            dist = (dist ^ 0xFF) + 1;
                            int addr = ofs+2-dist;
                            if (isLabel(addr)) {
                                printLabel("L"+hexLookup[(addr>>8)+0xC0]+hexLookup[addr&0xFF]);
                            }
                            else {
                                System.out.print("$-"+(ofs-2-addr));
                            }
                        }
                        newLine();
                    }
                    ofs += oplengthLookup[op];
                }
            }   // isCode(ofs)
            else if (isData(ofs)) { // print data table
                if (isLabel(ofs)) {
                    String label = "L"+hexLookup[(ofs>>8)+0xC0]+hexLookup[ofs&0xFF];
                    if (toHtml)
                        System.out.println("<A NAME="+label+"><BR>");
                    System.out.print(label+":");
                    newLine();
                }
                System.out.print(".DB $"+hexLookup[ROM[ofs++]]);
                int i=1;
                while ((ofs < 0x4000) && (map[ofs] == DATA)) {
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

/**
*
**/

    public static boolean isROMAddress(int ofs) {
        return ROM[ofs+1] >= 0x80;
    }

    public static void checkDataLabel(int ofs) {
        if (isROMAddress(ofs)) {
            int addr = getAddress(ofs);
            if (!isCode(addr)) {
                for (int i=1; i<4; i++) {
                    if ((addr-i > 0) && isData(addr-i) && isLabel(addr-i)) {
                        return;
                    }
                    if ((addr+i < 0x4000) && isData(addr+i) && isLabel(addr+i)) {
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
        for (int i=1; i<0x4000; i++) {
            if (isCode(i-1) && isData(i)) {
                map[i] |= LABEL;
            }
        }
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
        String label=null;
        if (isROMAddress(ofs)) {   // address is in ROM space (0xC000-0xFFFF)
            System.out.print(" ");
            int a = getAddress(ofs);
            if (!isLabel(a)) {  // no label exists for this address!
                for (int i=1; i<16; i++) {
                    if (isLabel(a-i)) { // no problem, use label of address-i
                        a-=i;
                        printLabel("L"+hexLookup[(a>>8)+0xC0]+hexLookup[a&0xFF]);
                        System.out.print("+"+i);
                        return;
                    }
                    else if (isLabel(a+i)) {    // no problem, use label of address+i
                        a+=i;
                        printLabel("L"+hexLookup[(a>>8)+0xC0]+hexLookup[a&0xFF]);
                        System.out.print("-"+i);
                        return;
                    }
                }
                // whoops, no label found, need to print hardcoded address...
                System.out.print("$"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
            }
            else {
                printLabel("L"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
            }
        }
        else {  // print address as direct memory offset ($XXXX)
	    if ((ROM[ofs+1] == 0) && needsWideningSuffixForZeroPageAddresses(op))
                System.out.print(".W");
            System.out.print(" ");
            System.out.print("$"+hexLookup[ROM[ofs+1]]+hexLookup[ROM[ofs]]);
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
        if ((ofs < 0) || (ofs >= 0x4000))
            return false;
        else
            return ((map[ofs] & CODE) != 0);
    }

/**
*
**/

    public static boolean isData(int ofs) {
        if ((ofs < 0) || (ofs >= 0x4000))
            return false;
        else
            return ((map[ofs] & DATA) != 0);
    }

/**
*
**/

    public static boolean isLabel(int ofs) {
        if ((ofs < 0) || (ofs >= 0x4000))
            return false;
        else
            return ((map[ofs] & LABEL) != 0);
    }

/**
*
**/

    public static boolean isPtr(int ofs) {
        if ((ofs < 0) || (ofs >= 0x4000))
            return false;
        else
            return ((map[ofs] & PTR) != 0);
    }

/**
*
**/

    public static boolean isInstr(int ofs) {
        if ((ofs < 0) || (ofs >= 0x4000))
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

}   // bye.
