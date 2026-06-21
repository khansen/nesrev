import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;

public class NESrevTest {
    private static int testsRun = 0;

    public static void main(String[] args) throws Exception {
        testGetAddressMasksTo14Bits();
        testVerifyDataLabelsMarksCodeToDataBoundary();
        testProcessCodeFollowsJsrTarget();
        testProcessCodeQueuesRelativeBranchTarget();
        testProcessCodeWrapsBackwardRelativeBranchAtRomStart();
        testProcessCodeWrapsForwardRelativeBranchAtRomEnd();
        testProcessCodeFollowsJmpIndirectThroughMirrorWindow();
        testPrintAddressAddsWideningSuffixForZeroPageAbsoluteOps();
        testPrintAddressKeepsMirrorOperandRaw();
        testCheckDataLabelAcceptsMirrorRomOperand();
        testOpcodeTablesHave256Entries();
        testProcessableOpcodesMapAsInstructions();
        testAddressingModesCoveredByProcessableOpcodes();
        testInlineCallsParseValid();
        testInlineCallsAcceptsLayoutWhitespaceAroundParens();
        testInlineCallsAcceptsAddressForms();
        testInlineCallsStripsCommentsAndBlankLines();
        testInlineCallsRejectsMissingHeader();
        testInlineCallsRejectsWrongHeader();
        testInlineCallsRejectsDuplicateCallee();
        testInlineCallsRejectsCountedNotFinal();
        testInlineCallsRejectsUnknownField();
        testInlineCallsRejectsBadBytesCount();
        testInlineCallsRejectsBadPointerKind();
        testInlineCallsRejectsBadPointerAdjustment();
        testInlineCallsRejectsAddressOutOfRange();
        testInlineCallsRejectsBadAddress();
        testInlineCallsRejectsMissingBar();
        testInlineCallsRejectsEmptyLayout();
        testInlineCallsRejectsTrailingComma();
        testInlineCallsEmptyConstant();
        testPointerTableConfigStripsComments();
        testDataRangesParseValid();
        testDataRangesAcceptsAddressForms();
        testDataRangesStripsCommentsAndBlankLines();
        testDataRangesRejectsMissingHeader();
        testDataRangesRejectsWrongHeader();
        testDataRangesRejectsZeroLength();
        testDataRangesRejectsNegativeLength();
        testDataRangesRejectsBadLength();
        testDataRangesRejectsExceedingRom();
        testDataRangesRejectsOverlap();
        testDataRangesRejectsTouching();
        testDataRangesRejectsAddressOutOfRange();
        testDataRangesEmptyConstant();
        testProcessCodeStopsAtBlockedByte();
        testApplyDataRangeBarriersBlocksAndLabels();
        testApplyDataRangeBarriersSeedsContinuation();
        testApplyDataRangeBarriersAtRomEndDoesNotSeedPastBoundary();
        testRestartLoopDiscoversAndAppliesCallsite();
        testRestartLoopDiscoversNestedCallsite();
        testResolveRecordRejectsAdjustedTargetOutOfRange();
        testResolveRecordValidatesJsrEncoding();
        testCountedRecordResumesAtCorrectByte();
        testPtrCodeAdjustmentSeedsAdjustedTarget();
        testPtrDataLabeledButNotTraced();
        testConflictDataRangeOverlapsInlineRecord();
        testConflictJsrTargetIsBlocked();
        testInlineRecordOutputFormatsDirectives();
        testDataRangeBoundaryDoesNotMergeWithAdjacentData();
        testInlineCallsRejectsUppercaseHeader();
        testDataRangesRejectsUppercaseHeader();
        testConflictRecordVsRecordOverlap();
        testConflictVectorTargetIsBlocked();
        testConflictCodeEntryTargetIsBlocked();
        testConflictCodePointerTargetIsBlocked();
        testCodePointerTableSkipsNonRomTarget();
        testCodePointerTableTracesMirrorWindowTarget();
        testDataPointerTableSkipsNonRomTarget();
        testConflictCodePointerTableByteIsBlocked();
        testConflictDataPointerTableByteIsBlocked();
        testConflictDataRangeContinuationTargetIsBlockedInlineRecord();
        testConflictJmpTargetIsBlocked();
        testConflictBranchTargetIsBlocked();
        testConflictInlinePtrCodeTargetIsBlocked();
        testConflictInstructionOperandStraddlesRange();
        testCountedPayloadOverrunFails();
        testRestartLoopNonConvergenceThrowsConfigException();
        testNoOptionOutputIsUnchanged();
        testNoOptionUnlabeledBackwardBranchOutputMatchesMaster();
        testSyntheticIntegrationReassembles();
        System.out.println("OK: " + testsRun + " tests passed.");
    }

    private static void testGetAddressMasksTo14Bits() throws Exception {
        resetState();
        int[] rom = new int[0x4000];
        rom[0] = 0x34;
        rom[1] = 0xF2;
        setField("ROM", rom);

        int addr = NESrev.getAddress(0);
        assertEquals("getAddress should return little-endian 14-bit value", 0x3234, addr);
    }

    private static void testVerifyDataLabelsMarksCodeToDataBoundary() throws Exception {
        resetState();
        int code = getIntField("CODE");
        int data = getIntField("DATA");
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        map[0] = code;
        setField("map", map);

        NESrev.verifyDataLabels();

        assertTrue("verifyDataLabels should set LABEL on code->data boundary", NESrev.isLabel(1));
    }

    private static void testProcessCodeFollowsJsrTarget() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // $C000: JSR $C010 ; RTS
        rom[0x0000] = 0x20;
        rom[0x0001] = 0x10;
        rom[0x0002] = 0xC0;
        rom[0x0003] = 0x60;
        // $C010: RTS
        rom[0x0010] = 0x60;

        setField("ROM", rom);
        setField("map", map);

        boolean mapped = NESrev.processCode(0x0000);
        assertTrue("processCode should map code at entry", mapped);
        assertTrue("entry should be code", NESrev.isCode(0x0000));
        assertTrue("JSR target should be code", NESrev.isCode(0x0010));
        assertTrue("JSR target should be instruction start", NESrev.isInstr(0x0010));
        assertTrue("mapped entry should become a label", NESrev.isLabel(0x0000));
    }

    private static void testProcessCodeQueuesRelativeBranchTarget() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // $C000: BNE +2 ; RTS ; RTS
        rom[0x0000] = 0xD0;
        rom[0x0001] = 0x02;
        rom[0x0002] = 0x60;
        rom[0x0004] = 0x60;

        setField("ROM", rom);
        setField("map", map);

        NESrev.processCode(0x0000);
        assertTrue("fallthrough after branch should be code", NESrev.isCode(0x0002));
        assertTrue("relative branch target should be code", NESrev.isCode(0x0004));
    }

    private static void testProcessCodeWrapsBackwardRelativeBranchAtRomStart() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // $C000: BNE -128 -> wraps to $3F82 in 14-bit space.
        rom[0x0000] = 0xD0;
        rom[0x0001] = 0x80;
        rom[0x0002] = 0x60;      // fallthrough stop
        rom[0x3F82] = 0x60;      // wrapped target stop

        setField("ROM", rom);
        setField("map", map);

        NESrev.processCode(0x0000);
        assertTrue("backward branch from start should wrap to 14-bit target", NESrev.isCode(0x3F82));
    }

    private static void testProcessCodeWrapsForwardRelativeBranchAtRomEnd() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // Start at $FFF0 (ofs 0x3FF0): BNE +127 from $FFF0+2 wraps to $0071 -> ofs 0x0071.
        rom[0x3FF0] = 0xD0;
        rom[0x3FF1] = 0x7F;
        rom[0x3FF2] = 0x60;      // fallthrough stop
        rom[0x0071] = 0x60;      // wrapped target stop

        setField("ROM", rom);
        setField("map", map);

        NESrev.processCode(0x3FF0);
        assertTrue("forward branch near end should wrap to 14-bit target", NESrev.isCode(0x0071));
    }

    private static void testProcessCodeFollowsJmpIndirectThroughMirrorWindow() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // $C000: JMP ($8004). On NROM-128, $8004 mirrors PRG offset $0004.
        rom[0x0000] = 0x6C;
        rom[0x0001] = 0x04;
        rom[0x0002] = 0x80;
        rom[0x0004] = 0x10;
        rom[0x0005] = 0xC0;
        rom[0x0010] = 0x60;

        setField("ROM", rom);
        setField("map", map);

        NESrev.processCode(0x0000);
        assertTrue("JMP indirect mirror operand should trace target", NESrev.isCode(0x0010));
        assertTrue("JMP indirect mirror target should be instruction start", NESrev.isInstr(0x0010));
    }

    private static void testPrintAddressAddsWideningSuffixForZeroPageAbsoluteOps() throws Exception {
        resetState();
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        setField("ROM", rom);
        setField("map", map);

        // Address operand bytes for $006B.
        rom[0x0100] = 0x6B;
        rom[0x0101] = 0x00;

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        System.setOut(new PrintStream(baos));
        try {
            NESrev.printAddress(0x0100, 0xAD); // LDA abs
        } finally {
            System.setOut(originalOut);
        }

        String rendered = baos.toString();
        assertEquals("printAddress should include .W for $00xx absolute opcodes", ".W $006B", rendered);
    }

    private static void testPrintAddressKeepsMirrorOperandRaw() throws Exception {
        resetState();
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        setField("ROM", rom);
        setField("map", map);

        // Operand $8004 mirrors PRG offset $0004. Even if analysis labels that
        // PRG byte, output must preserve the literal mirror operand.
        rom[0x0100] = 0x04;
        rom[0x0101] = 0x80;
        map[0x0004] |= getIntField("LABEL");

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        System.setOut(new PrintStream(baos));
        try {
            NESrev.printAddress(0x0100, 0xAD); // LDA abs
        } finally {
            System.setOut(originalOut);
        }

        assertEquals("printAddress should preserve mirror operand", " $8004", baos.toString());
    }

    private static void testCheckDataLabelAcceptsMirrorRomOperand() throws Exception {
        resetState();
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        int data = getIntField("DATA");
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // Operand $8004 mirrors PRG offset $0004 and should still be labeled
        // for analysis/data-boundary purposes.
        rom[0x0100] = 0x04;
        rom[0x0101] = 0x80;

        setField("ROM", rom);
        setField("map", map);

        NESrev.checkDataLabel(0x0100);
        assertTrue("mirror ROM operand should label mirrored PRG byte", NESrev.isLabel(0x0004));
    }

    private static void testOpcodeTablesHave256Entries() throws Exception {
        String[] mnemonicLookup = (String[]) getField("mnemonicLookup");
        int[] opaddrmodeLookup = (int[]) getField("opaddrmodeLookup");
        int[] oplengthLookup = (int[]) getField("oplengthLookup");
        boolean[] processable = (boolean[]) getField("PROCESSABLE_OPCODE");

        assertEquals("mnemonic table should have 256 entries", 256, mnemonicLookup.length);
        assertEquals("address-mode table should have 256 entries", 256, opaddrmodeLookup.length);
        assertEquals("length table should have 256 entries", 256, oplengthLookup.length);
        assertEquals("processable opcode table should have 256 entries", 256, processable.length);
    }

    private static void testProcessableOpcodesMapAsInstructions() throws Exception {
        int[] opaddrmodeLookup = (int[]) getField("opaddrmodeLookup");
        int[] oplengthLookup = (int[]) getField("oplengthLookup");
        boolean[] processable = (boolean[]) getField("PROCESSABLE_OPCODE");
        String[] mnemonicLookup = (String[]) getField("mnemonicLookup");
        int undf = getIntField("UNDF");

        for (int op = 0; op < 256; op++) {
            if (!processable[op]) {
                continue;
            }
            resetState();
            int[] rom = new int[0x4000];
            int[] map = new int[0x4000];
            int data = getIntField("DATA");
            for (int i = 0; i < map.length; i++) {
                map[i] = data;
            }
            rom[0] = op;
            int len = oplengthLookup[op];
            if (len >= 2) {
                // Safe defaults for operand bytes; for rel-branches keep local target.
                rom[1] = 0x00;
            }
            if (len >= 3) {
                rom[2] = 0x00;
            }
            // Ensure we can stop linearly when needed right after this opcode.
            if (len < rom.length) {
                rom[len] = 0x60; // RTS
            }

            setField("ROM", rom);
            setField("map", map);

            boolean mapped = NESrev.processCode(0);
            assertTrue("processable opcode should map code: " + hex(op), mapped);
            assertTrue("processable opcode should mark instruction start: " + hex(op), NESrev.isInstr(0));
            assertTrue("processable opcode should mark code start: " + hex(op), NESrev.isCode(0));
            assertTrue("processable opcode should have non-undefined mode: " + hex(op), opaddrmodeLookup[op] != undf);
            assertTrue("processable opcode should have positive length: " + hex(op), len > 0);
            assertTrue("processable opcode mnemonic should not be ???: " + hex(op), !mnemonicLookup[op].equals("???"));
        }
    }

    private static void testAddressingModesCoveredByProcessableOpcodes() throws Exception {
        int[] opaddrmodeLookup = (int[]) getField("opaddrmodeLookup");
        boolean[] processable = (boolean[]) getField("PROCESSABLE_OPCODE");

        int impl = getIntField("IMPL");
        int immd = getIntField("IMMD");
        int zero = getIntField("ZERO");
        int zerx = getIntField("ZERX");
        int zery = getIntField("ZERY");
        int absl = getIntField("ABSL");
        int absx = getIntField("ABSX");
        int absy = getIntField("ABSY");
        int indr = getIntField("INDR");
        int indx = getIntField("INDX");
        int indy = getIntField("INDY");
        int relv = getIntField("RELV");

        Set<Integer> seenModes = new HashSet<Integer>();
        for (int op = 0; op < 256; op++) {
            if (processable[op]) {
                seenModes.add(opaddrmodeLookup[op]);
            }
        }

        assertTrue("IMPL mode should be covered", seenModes.contains(impl));
        assertTrue("IMMD mode should be covered", seenModes.contains(immd));
        assertTrue("ZERO mode should be covered", seenModes.contains(zero));
        assertTrue("ZERX mode should be covered", seenModes.contains(zerx));
        assertTrue("ZERY mode should be covered", seenModes.contains(zery));
        assertTrue("ABSL mode should be covered", seenModes.contains(absl));
        assertTrue("ABSX mode should be covered", seenModes.contains(absx));
        assertTrue("ABSY mode should be covered", seenModes.contains(absy));
        assertTrue("INDR mode should be covered", seenModes.contains(indr));
        assertTrue("INDX mode should be covered", seenModes.contains(indx));
        assertTrue("INDY mode should be covered", seenModes.contains(indy));
        assertTrue("RELV mode should be covered", seenModes.contains(relv));
    }

    private static void testInlineCallsParseValid() throws Exception {
        File f = writeTempConfig("inlinecalls",
            "callee|layout\n"
            + "$EB0A|u8,ptr16(code,+1)\n"
            + "$EA17|counted8\n"
            + "$C963|bytes(6)\n"
            + "$C8BB|u8,ptr16(data)\n");
        NESrev.InlineCallsConfig cfg = NESrev.InlineCallsConfig.parse(f.getAbsolutePath());
        assertEquals("inlinecalls entry count", 4, cfg.entries.length);

        NESrev.InlineCallEntry eb0a = cfg.findByCallee(0xEB0A & 0x3FFF);
        assertNotNull("EB0A entry exists", eb0a);
        assertEquals("EB0A CPU address", 0xEB0A, eb0a.calleeCpu);
        assertEquals("EB0A layout field count", 2, eb0a.layout.fields.length);
        assertEquals("EB0A field[0] kind", NESrev.InlineField.U8, eb0a.layout.fields[0].kind);
        assertEquals("EB0A field[0] byteCount", 1, eb0a.layout.fields[0].byteCount);
        assertEquals("EB0A field[1] kind", NESrev.InlineField.PTR16, eb0a.layout.fields[1].kind);
        assertEquals("EB0A field[1] pointerKind", NESrev.PointerKind.CODE, eb0a.layout.fields[1].pointerKind);
        assertEquals("EB0A field[1] adjustment", 1, eb0a.layout.fields[1].pointerAdjustment);
        assertEquals("EB0A fixedSize", 3, eb0a.layout.fixedSize);
        assertFalse("EB0A is not variable", eb0a.layout.hasCounted8);

        NESrev.InlineCallEntry ea17 = cfg.findByCallee(0xEA17 & 0x3FFF);
        assertNotNull("EA17 entry exists", ea17);
        assertEquals("EA17 layout field count", 1, ea17.layout.fields.length);
        assertEquals("EA17 field[0] kind", NESrev.InlineField.COUNTED8, ea17.layout.fields[0].kind);
        assertTrue("EA17 is variable", ea17.layout.hasCounted8);

        NESrev.InlineCallEntry c963 = cfg.findByCallee(0xC963 & 0x3FFF);
        assertNotNull("C963 entry exists", c963);
        assertEquals("C963 field[0] kind", NESrev.InlineField.BYTES, c963.layout.fields[0].kind);
        assertEquals("C963 field[0] byteCount", 6, c963.layout.fields[0].byteCount);
        assertEquals("C963 fixedSize", 6, c963.layout.fixedSize);

        NESrev.InlineCallEntry c8bb = cfg.findByCallee(0xC8BB & 0x3FFF);
        assertNotNull("C8BB entry exists", c8bb);
        assertEquals("C8BB field[1] kind", NESrev.InlineField.PTR16, c8bb.layout.fields[1].kind);
        assertEquals("C8BB field[1] pointerKind", NESrev.PointerKind.DATA, c8bb.layout.fields[1].pointerKind);
        assertEquals("C8BB field[1] adjustment", 0, c8bb.layout.fields[1].pointerAdjustment);
    }

    private static void testInlineCallsAcceptsLayoutWhitespaceAroundParens() throws Exception {
        File f = writeTempConfig("inlinecalls-layout-ws",
            "callee|layout\n"
            + "$EB0A|bytes ( 6 ), ptr16 ( code , +1 )\n");
        NESrev.InlineCallsConfig cfg = NESrev.InlineCallsConfig.parse(f.getAbsolutePath());

        NESrev.InlineCallEntry entry = cfg.findByCallee(0xEB0A & 0x3FFF);
        assertNotNull("EB0A entry exists", entry);
        assertEquals("field count", 2, entry.layout.fields.length);
        assertEquals("bytes field kind", NESrev.InlineField.BYTES, entry.layout.fields[0].kind);
        assertEquals("bytes count", 6, entry.layout.fields[0].byteCount);
        assertEquals("ptr16 field kind", NESrev.InlineField.PTR16, entry.layout.fields[1].kind);
        assertEquals("ptr16 pointer kind", NESrev.PointerKind.CODE, entry.layout.fields[1].pointerKind);
        assertEquals("ptr16 adjustment", 1, entry.layout.fields[1].pointerAdjustment);
    }

    private static void testInlineCallsAcceptsAddressForms() throws Exception {
        File f = writeTempConfig("inlinecalls-addrs",
            "callee|layout\n"
            + "$EB0A|u8\n"
            + "0xEA17|u8\n"
            + "EA63|u8\n");
        NESrev.InlineCallsConfig cfg = NESrev.InlineCallsConfig.parse(f.getAbsolutePath());
        assertEquals("entry count", 3, cfg.entries.length);
        assertNotNull("$EB0A", cfg.findByCallee(0xEB0A & 0x3FFF));
        assertNotNull("0xEA17", cfg.findByCallee(0xEA17 & 0x3FFF));
        assertNotNull("bare EA63", cfg.findByCallee(0xEA63 & 0x3FFF));
    }

    private static void testInlineCallsStripsCommentsAndBlankLines() throws Exception {
        File f = writeTempConfig("inlinecalls-comments",
            "# leading comment\n"
            + "\n"
            + "callee|layout   # header comment\n"
            + "\n"
            + "; second comment style\n"
            + "$EB0A|u8,ptr16(code,+1)  ; trailing\n"
            + "  $EA17  |  counted8  \n");
        NESrev.InlineCallsConfig cfg = NESrev.InlineCallsConfig.parse(f.getAbsolutePath());
        assertEquals("entry count", 2, cfg.entries.length);
    }

    private static void testInlineCallsRejectsMissingHeader() throws Exception {
        File f = writeTempConfig("inlinecalls-no-header", "# only comments\n\n");
        expectConfigError("missing header rejected",
            f.getAbsolutePath(), true, "missing header");
    }

    private static void testInlineCallsRejectsWrongHeader() throws Exception {
        File f = writeTempConfig("inlinecalls-wrong-header",
            "name|layout\n$EB0A|u8\n");
        expectConfigError("wrong header rejected",
            f.getAbsolutePath(), true, "expected header");
    }

    private static void testInlineCallsRejectsDuplicateCallee() throws Exception {
        File f = writeTempConfig("inlinecalls-dup",
            "callee|layout\n$EB0A|u8\n$EB0A|counted8\n");
        expectConfigError("duplicate callee rejected",
            f.getAbsolutePath(), true, "duplicate callee");
    }

    private static void testInlineCallsRejectsCountedNotFinal() throws Exception {
        File f = writeTempConfig("inlinecalls-counted-not-final",
            "callee|layout\n$EB0A|counted8,u8\n");
        expectConfigError("counted8 must be final",
            f.getAbsolutePath(), true, "counted8");
    }

    private static void testInlineCallsRejectsUnknownField() throws Exception {
        File f = writeTempConfig("inlinecalls-unknown-field",
            "callee|layout\n$EB0A|u16\n");
        expectConfigError("unknown field rejected",
            f.getAbsolutePath(), true, "unknown field");
    }

    private static void testInlineCallsRejectsBadBytesCount() throws Exception {
        File f = writeTempConfig("inlinecalls-bytes-zero",
            "callee|layout\n$EB0A|bytes(0)\n");
        expectConfigError("bytes(0) rejected",
            f.getAbsolutePath(), true, "'bytes(N)' requires N > 0");

        File f2 = writeTempConfig("inlinecalls-bytes-noparen",
            "callee|layout\n$EB0A|bytes\n");
        expectConfigError("bytes without ( rejected",
            f2.getAbsolutePath(), true, "'bytes'");
    }

    private static void testInlineCallsRejectsBadPointerKind() throws Exception {
        File f = writeTempConfig("inlinecalls-ptr-kind",
            "callee|layout\n$EB0A|ptr16(other)\n");
        expectConfigError("ptr16 unknown kind rejected",
            f.getAbsolutePath(), true, "kind must be 'code' or 'data'");
    }

    private static void testInlineCallsRejectsBadPointerAdjustment() throws Exception {
        File f = writeTempConfig("inlinecalls-ptr-adj",
            "callee|layout\n$EB0A|ptr16(code,abc)\n");
        expectConfigError("ptr16 bad adjustment rejected",
            f.getAbsolutePath(), true, "adjustment must be a signed integer");
    }

    private static void testInlineCallsRejectsAddressOutOfRange() throws Exception {
        File f = writeTempConfig("inlinecalls-oor",
            "callee|layout\n$8000|u8\n");
        expectConfigError("address out of $C000-$FFFF rejected",
            f.getAbsolutePath(), true, "out of $C000-$FFFF range");
    }

    private static void testInlineCallsRejectsBadAddress() throws Exception {
        File f = writeTempConfig("inlinecalls-badaddr",
            "callee|layout\nXYZ|u8\n");
        expectConfigError("non-hex address rejected",
            f.getAbsolutePath(), true, "bad CPU address");
    }

    private static void testInlineCallsRejectsMissingBar() throws Exception {
        File f = writeTempConfig("inlinecalls-no-bar",
            "callee|layout\n$EB0A u8\n");
        expectConfigError("missing | rejected",
            f.getAbsolutePath(), true, "missing '|'");
    }

    private static void testInlineCallsRejectsEmptyLayout() throws Exception {
        File f = writeTempConfig("inlinecalls-empty-layout",
            "callee|layout\n$EB0A|\n");
        expectConfigError("empty layout rejected",
            f.getAbsolutePath(), true, "empty layout");
    }

    private static void testInlineCallsRejectsTrailingComma() throws Exception {
        File f = writeTempConfig("inlinecalls-trailing-comma",
            "callee|layout\n$EB0A|u8,\n");
        expectConfigError("trailing comma rejected",
            f.getAbsolutePath(), true, "trailing ','");
    }

    private static void testInlineCallsEmptyConstant() throws Exception {
        assertTrue("EMPTY isEmpty", NESrev.InlineCallsConfig.EMPTY.isEmpty());
        assertEquals("EMPTY entry count", 0, NESrev.InlineCallsConfig.EMPTY.entries.length);
    }

    private static void testPointerTableConfigStripsComments() throws Exception {
        File f = writeTempConfig("pointer-comments",
            "# leading comment\n"
            + "; semicolon comment\n"
            + "start|count   # header comment\n"
            + "0x0100|2      ; inline semicolon\n"
            + "0x0200|1      # inline hash\n");
        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        java.lang.reflect.Method m = NESrev.class.getDeclaredMethod("parsePointerTableConfig",
            String.class, String.class, java.util.ArrayList.class, java.util.ArrayList.class);
        m.setAccessible(true);

        m.invoke(null, f.getAbsolutePath(), "code pointer", starts, counts);

        assertEquals("pointer table row count", 2, starts.size());
        assertEquals("first pointer start", 0x0100, starts.get(0).intValue());
        assertEquals("first pointer count", 2, counts.get(0).intValue());
        assertEquals("second pointer start", 0x0200, starts.get(1).intValue());
        assertEquals("second pointer count", 1, counts.get(1).intValue());
    }

    private static void testDataRangesParseValid() throws Exception {
        File f = writeTempConfig("dataranges-valid",
            "start|length\n"
            + "$CD20|14\n"
            + "$CE1A|8\n"
            + "$D5B6|34\n"
            + "$D84F|12\n");
        NESrev.DataRangesConfig cfg = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        assertEquals("range count", 4, cfg.entries.length);

        // Entries are sorted by start.
        assertEquals("range[0] CPU start", 0xCD20, cfg.entries[0].startCpu);
        assertEquals("range[0] start", 0xCD20 & 0x3FFF, cfg.entries[0].start);
        assertEquals("range[0] length", 14, cfg.entries[0].length);
        assertEquals("range[0] end", (0xCD20 & 0x3FFF) + 14, cfg.entries[0].end);

        assertEquals("range[3] CPU start", 0xD84F, cfg.entries[3].startCpu);
        assertEquals("range[3] length", 12, cfg.entries[3].length);
    }

    private static void testDataRangesAcceptsAddressForms() throws Exception {
        File f = writeTempConfig("dataranges-addrs",
            "start|length\n"
            + "$CD20|2\n"
            + "0xCE1A|2\n"
            + "D5B6|2\n");
        NESrev.DataRangesConfig cfg = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        assertEquals("range count", 3, cfg.entries.length);
    }

    private static void testDataRangesStripsCommentsAndBlankLines() throws Exception {
        File f = writeTempConfig("dataranges-comments",
            "# leading\n\nstart|length\n; another comment\n$CD20|14   # explanatory\n");
        NESrev.DataRangesConfig cfg = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        assertEquals("range count", 1, cfg.entries.length);
        assertEquals("range CPU start", 0xCD20, cfg.entries[0].startCpu);
    }

    private static void testDataRangesRejectsMissingHeader() throws Exception {
        File f = writeTempConfig("dataranges-no-header", "# only comments\n\n");
        expectConfigError("missing header rejected",
            f.getAbsolutePath(), false, "missing header");
    }

    private static void testDataRangesRejectsWrongHeader() throws Exception {
        File f = writeTempConfig("dataranges-wrong-header",
            "begin|size\n$CD20|14\n");
        expectConfigError("wrong header rejected",
            f.getAbsolutePath(), false, "expected header");
    }

    private static void testDataRangesRejectsZeroLength() throws Exception {
        File f = writeTempConfig("dataranges-zero",
            "start|length\n$CD20|0\n");
        expectConfigError("zero length rejected",
            f.getAbsolutePath(), false, "must be > 0");
    }

    private static void testDataRangesRejectsNegativeLength() throws Exception {
        File f = writeTempConfig("dataranges-neg",
            "start|length\n$CD20|-4\n");
        expectConfigError("negative length rejected",
            f.getAbsolutePath(), false, "must be > 0");
    }

    private static void testDataRangesRejectsBadLength() throws Exception {
        File f = writeTempConfig("dataranges-bad-len",
            "start|length\n$CD20|abc\n");
        expectConfigError("non-numeric length rejected",
            f.getAbsolutePath(), false, "positive decimal integer");
    }

    private static void testDataRangesRejectsExceedingRom() throws Exception {
        // $FFFE + 8 spills past $10000 ROM boundary.
        File f = writeTempConfig("dataranges-overflow",
            "start|length\n$FFFE|8\n");
        expectConfigError("range past ROM rejected",
            f.getAbsolutePath(), false, "exceeds ROM");
    }

    private static void testDataRangesRejectsOverlap() throws Exception {
        File f = writeTempConfig("dataranges-overlap",
            "start|length\n$CD20|16\n$CD28|4\n");
        expectConfigError("overlapping ranges rejected",
            f.getAbsolutePath(), false, "overlap");
    }

    private static void testDataRangesRejectsTouching() throws Exception {
        File f = writeTempConfig("dataranges-touch",
            "start|length\n$CD20|8\n$CD28|4\n");
        expectConfigError("touching ranges rejected",
            f.getAbsolutePath(), false, "touch");
    }

    private static void testDataRangesRejectsAddressOutOfRange() throws Exception {
        File f = writeTempConfig("dataranges-oor",
            "start|length\n$8000|4\n");
        expectConfigError("address out of $C000-$FFFF rejected",
            f.getAbsolutePath(), false, "out of $C000-$FFFF range");
    }

    private static void testDataRangesEmptyConstant() throws Exception {
        assertTrue("EMPTY isEmpty", NESrev.DataRangesConfig.EMPTY.isEmpty());
        assertEquals("EMPTY entry count", 0, NESrev.DataRangesConfig.EMPTY.entries.length);
    }

    private static File writeTempConfig(String namePrefix, String content) throws Exception {
        File f = File.createTempFile("nesrev-" + namePrefix + "-", ".csv");
        f.deleteOnExit();
        try (FileWriter w = new FileWriter(f)) {
            w.write(content);
        }
        return f;
    }

    private static void expectConfigError(String label, String path, boolean inlineCalls, String expectedFragment) {
        try {
            if (inlineCalls) {
                NESrev.InlineCallsConfig.parse(path);
            } else {
                NESrev.DataRangesConfig.parse(path);
            }
            testsRun++;
            throw new AssertionError(label + ": expected ConfigException, got success");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains(expectedFragment)) {
                throw new AssertionError(label + ": message did not contain '"
                    + expectedFragment + "' (got: " + ex.getMessage() + ")");
            }
        }
    }

    private static void assertNotNull(String msg, Object value) {
        testsRun++;
        if (value == null) {
            throw new AssertionError(msg + ": value was null");
        }
    }

    private static void assertFalse(String msg, boolean condition) {
        testsRun++;
        if (condition) {
            throw new AssertionError(msg);
        }
    }

    private static void testProcessCodeStopsAtBlockedByte() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // $C000: NOP ; NOP ; RTS — but byte at $C001 is blocked.
        // Linear flow decodes $C000 (NOP, 1 byte), then would step into the
        // blocked byte at $C001 and must stop there.
        rom[0x0000] = 0xEA; // NOP
        rom[0x0001] = 0xEA; // would be NOP if not blocked
        rom[0x0002] = 0x60; // RTS

        boolean[] blocked = new boolean[0x4000];
        blocked[0x0001] = true;

        setField("ROM", rom);
        setField("map", map);
        setField("blockedFromCode", blocked);

        NESrev.processCode(0x0000);
        assertTrue("entry should be code", NESrev.isCode(0x0000));
        assertFalse("blocked byte should not become code", NESrev.isCode(0x0001));
        assertFalse("byte after blocked byte should not be reached linearly",
            NESrev.isCode(0x0002));
    }

    private static void testApplyDataRangeBarriersBlocksAndLabels() throws Exception {
        resetState();
        // Configure a single 8-byte data range at $CE1A (PRG 0x0E1A).
        NESrev.DataRangeEntry entry = new NESrev.DataRangeEntry(0x0E1A, 0xCE1A, 8, 1);
        NESrev.DataRangesConfig cfg = new NESrev.DataRangesConfig(new NESrev.DataRangeEntry[]{ entry });
        setField("dataRanges", cfg);

        NESrev.applyDataRangeBarriers();

        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        for (int i = 0; i < 8; i++) {
            assertTrue("byte $CE1A+" + i + " blocked", blocked[0x0E1A + i]);
        }
        assertFalse("byte before range not blocked", blocked[0x0E19]);
        assertFalse("byte at end of range not blocked", blocked[0x0E22]);

        assertTrue("range start labeled", NESrev.isLabel(0x0E1A));

        // Reset config to EMPTY so it doesn't leak into the next test.
        setField("dataRanges", NESrev.DataRangesConfig.EMPTY);
    }

    private static void testApplyDataRangeBarriersSeedsContinuation() throws Exception {
        resetState();
        int data = getIntField("DATA");
        int[] rom = new int[0x4000];
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        // After the data range at $CE1A+8, the byte at $CE22 (PRG 0x0E22) is
        // RTS — applying the barrier should seed it as a code continuation.
        rom[0x0E22] = 0x60;

        setField("ROM", rom);
        setField("map", map);

        NESrev.DataRangeEntry entry = new NESrev.DataRangeEntry(0x0E1A, 0xCE1A, 8, 1);
        NESrev.DataRangesConfig cfg = new NESrev.DataRangesConfig(new NESrev.DataRangeEntry[]{ entry });
        setField("dataRanges", cfg);

        NESrev.applyDataRangeBarriers();

        assertTrue("range end labeled", NESrev.isLabel(0x0E22));
        assertTrue("range end traced as code", NESrev.isCode(0x0E22));

        setField("dataRanges", NESrev.DataRangesConfig.EMPTY);
    }

    private static void testApplyDataRangeBarriersAtRomEndDoesNotSeedPastBoundary() throws Exception {
        resetState();
        // Range that fills exactly to the ROM boundary: $FFF8 + 8 = $10000.
        NESrev.DataRangeEntry entry = new NESrev.DataRangeEntry(0x3FF8, 0xFFF8, 8, 1);
        NESrev.DataRangesConfig cfg = new NESrev.DataRangesConfig(new NESrev.DataRangeEntry[]{ entry });
        setField("dataRanges", cfg);

        NESrev.applyDataRangeBarriers();

        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        assertTrue("first byte of range blocked", blocked[0x3FF8]);
        assertTrue("last byte of range blocked", blocked[0x3FFF]);
        assertTrue("start labeled", NESrev.isLabel(0x3FF8));
        // No continuation seed past ROM boundary.

        setField("dataRanges", NESrev.DataRangesConfig.EMPTY);
    }

    private static void testRestartLoopDiscoversAndAppliesCallsite() throws Exception {
        resetState();
        // ROM: vector at $FFFC -> $C000.
        // $C000: JSR $CFFE ; data $AA $BB ; RTS (continuation)
        // $CFFE: RTS
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF; // JSR $CFFE
        rom[0x0003] = 0xAA; rom[0x0004] = 0xBB;                     // inline record
        rom[0x0005] = 0x60;                                         // RTS continuation
        rom[0x0FFE] = 0x60;                                         // callee body at PRG $0FFE (CPU $CFFE)
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;                     // reset vector -> $C000
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|bytes(2)\n");

        NESrev.runAnalysisToFixedPoint();

        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        assertTrue("record byte $C003 blocked", blocked[0x0003]);
        assertTrue("record byte $C004 blocked", blocked[0x0004]);
        assertFalse("continuation byte $C005 not blocked", blocked[0x0005]);

        assertTrue("record start $C003 labeled", NESrev.isLabel(0x0003));
        assertTrue("continuation $C005 labeled", NESrev.isLabel(0x0005));
        assertTrue("continuation $C005 traced as code", NESrev.isCode(0x0005));
        assertTrue("callee $CFFE traced as code", NESrev.isCode(0x0FFE));
        assertFalse("record byte $C003 not code", NESrev.isCode(0x0003));
        assertFalse("record byte $C004 not code", NESrev.isCode(0x0004));

        TreeMap<?, ?> known = (TreeMap<?, ?>) getField("knownCallsites");
        assertEquals("one resolved callsite", 1, known.size());
    }

    private static void testRestartLoopDiscoversNestedCallsite() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; inline byte $AA ; JSR $CFFA ; inline byte $BB ; RTS
        // $CFFA: RTS  (configured callee with bytes(1) record)
        // $CFFE: RTS  (configured callee with bytes(1) record)
        // The nested JSR is inside the continuation of the first record, so it
        // can't be discovered until pass 2.
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF; // JSR $CFFE
        rom[0x0003] = 0xAA;                                         // inline byte for first callsite
        rom[0x0004] = 0x20; rom[0x0005] = 0xFA; rom[0x0006] = 0xCF; // JSR $CFFA
        rom[0x0007] = 0xBB;                                         // inline byte for second callsite
        rom[0x0008] = 0x60;                                         // final RTS
        rom[0x0FFA] = 0x60;                                         // $CFFA body at PRG $0FFA
        rom[0x0FFE] = 0x60;                                         // $CFFE body at PRG $0FFE
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig(
            "callee|layout\n"
            + "$CFFA|bytes(1)\n"
            + "$CFFE|bytes(1)\n");

        NESrev.runAnalysisToFixedPoint();

        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        assertTrue("first record byte $C003 blocked", blocked[0x0003]);
        assertTrue("second record byte $C007 blocked", blocked[0x0007]);
        assertTrue("continuation $C004 is code (JSR opcode)", NESrev.isCode(0x0004));
        assertTrue("continuation $C008 is code (final RTS)", NESrev.isCode(0x0008));

        TreeMap<?, ?> known = (TreeMap<?, ?>) getField("knownCallsites");
        assertEquals("two resolved callsites", 2, known.size());
    }

    private static void testResolveRecordRejectsAdjustedTargetOutOfRange() throws Exception {
        resetState();
        int[] rom = makeRom();
        // JSR $CFFE encoded; record encodes $4000+1 = $4001 (out of ROM), adjustment +1.
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0x00; rom[0x0004] = 0x40; // encoded $4000 -> +1 -> $4001 OOR
        setField("ROM", rom);

        loadInlineCallsConfig("callee|layout\n$CFFE|ptr16(code,+1)\n");
        NESrev.InlineCallsConfig cfg = (NESrev.InlineCallsConfig) getField("inlineCalls");
        NESrev.InlineCallEntry entry = cfg.findByCallee(0x0FFE);

        try {
            NESrev.resolveRecord(0x0000, entry);
            testsRun++;
            throw new AssertionError("expected ConfigException for adjusted target out of range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("outside canonical ROM space")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testResolveRecordValidatesJsrEncoding() throws Exception {
        resetState();
        int[] rom = makeRom();
        // Wrong opcode at callsite.
        rom[0x0000] = 0xEA; // NOP, not JSR
        rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        setField("ROM", rom);

        loadInlineCallsConfig("callee|layout\n$CFFE|u8\n");
        NESrev.InlineCallsConfig cfg = (NESrev.InlineCallsConfig) getField("inlineCalls");
        NESrev.InlineCallEntry entry = cfg.findByCallee(0x0FFE);
        try {
            NESrev.resolveRecord(0x0000, entry);
            testsRun++;
            throw new AssertionError("expected ConfigException for non-JSR opcode");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("expected JSR")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testCountedRecordResumesAtCorrectByte() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; count=3 ; A1 A2 A3 ; RTS
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0x03;                          // count
        rom[0x0004] = 0xA1; rom[0x0005] = 0xA2; rom[0x0006] = 0xA3; // payload (opcode-like bytes)
        rom[0x0007] = 0x60;                          // continuation RTS
        rom[0x0FFE] = 0x60;                          // callee at PRG $0FFE
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|counted8\n");
        NESrev.runAnalysisToFixedPoint();

        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        for (int i = 0x0003; i <= 0x0006; i++) {
            assertTrue("counted byte $" + Integer.toHexString(0xC000 + i) + " blocked", blocked[i]);
        }
        assertFalse("continuation $C007 not blocked", blocked[0x0007]);
        assertTrue("continuation $C007 traced as code", NESrev.isCode(0x0007));
        assertTrue("record start $C003 labeled", NESrev.isLabel(0x0003));
        assertTrue("continuation $C007 labeled", NESrev.isLabel(0x0007));
    }

    private static void testPtrCodeAdjustmentSeedsAdjustedTarget() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; .DW $D000-1 (encoded $CFFF, adjusted -> $D000) ; RTS
        // $D000: RTS (the adjusted target)
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0xFF; rom[0x0004] = 0xCF;       // encoded $CFFF
        rom[0x0005] = 0x60;                            // continuation
        rom[0x0FFE] = 0x60;                            // callee at PRG $0FFE
        rom[0x1000] = 0x60;                            // $D000 target (PRG offset 0x1000)
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|ptr16(code,+1)\n");
        NESrev.runAnalysisToFixedPoint();

        assertTrue("adjusted code target $D000 labeled", NESrev.isLabel(0x1000));
        assertTrue("adjusted code target $D000 traced as code", NESrev.isCode(0x1000));
        assertTrue("record start $C003 labeled", NESrev.isLabel(0x0003));
        assertTrue("continuation $C005 traced", NESrev.isCode(0x0005));
    }

    private static void testPtrDataLabeledButNotTraced() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; .DW $D100 (no adjustment) ; RTS
        // $D100: $AD (LDA abs opcode-like byte) — must remain data.
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0x00; rom[0x0004] = 0xD1;       // encoded $D100
        rom[0x0005] = 0x60;                            // continuation
        rom[0x0FFE] = 0x60;                            // callee at PRG $0FFE
        rom[0x1100] = 0xAD; rom[0x1101] = 0x00; rom[0x1102] = 0x00; // looks like LDA $0000
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|ptr16(data)\n");
        NESrev.runAnalysisToFixedPoint();

        assertTrue("data target $D100 labeled", NESrev.isLabel(0x1100));
        assertFalse("data target $D100 NOT traced as code", NESrev.isCode(0x1100));
    }

    private static void testConflictDataRangeOverlapsInlineRecord() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; bytes(2) record at $C003-$C004 ; RTS at $C005
        // Then configure a data range $C004+4 that overlaps the record.
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0xAA; rom[0x0004] = 0xBB;
        rom[0x0005] = 0x60;
        rom[0x0FFE] = 0x60;
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|bytes(2)\n");
        File f = writeTempConfig("conflict-overlap",
            "start|length\n$C004|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for record/range overlap");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("overlaps already-blocked byte")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictJsrTargetIsBlocked() throws Exception {
        resetState();
        // $C000: JSR $CE1A — target is inside a configured data range.
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0x1A; rom[0x0002] = 0xCE; // JSR $CE1A
        rom[0x0003] = 0x60;
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        File f = writeTempConfig("conflict-jsr",
            "start|length\n$CE1A|8\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for JSR into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("inline-data conflict")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
            if (!ex.getMessage().contains("JSR at $C000")) {
                throw new AssertionError("missing source description: " + ex.getMessage());
            }
        }
    }

    private static void testInlineRecordOutputFormatsDirectives() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; u8=$05 ; ptr16(code,+1) encoded $CFFF (target $D000)
        //        ; RTS at $C006
        // $CFFE: RTS
        // $D000: RTS  (target of adjusted pointer)
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0x05;                            // u8
        rom[0x0004] = 0xFF; rom[0x0005] = 0xCF;        // encoded $CFFF -> target $D000
        rom[0x0006] = 0x60;                            // continuation
        rom[0x0FFE] = 0x60;                            // callee
        rom[0x1000] = 0x60;                            // adjusted pointer target
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|u8,ptr16(code,+1)\n");
        NESrev.runAnalysisToFixedPoint();

        String output = captureDisassemble();
        assertContainsLine(output, "LC003:");
        assertContainsLine(output, ".DB $05");
        assertContainsLine(output, ".DW LD000-1");
    }

    private static void testDataRangeBoundaryDoesNotMergeWithAdjacentData() throws Exception {
        resetState();
        // Configure a data range $CE1A length 4. Surround with adjacent data
        // (no code paths through it). Verify the range emits as its own .DB
        // block and doesn't merge with adjacent generic data.
        int[] rom = makeRom();
        rom[0x0E18] = 0x11; rom[0x0E19] = 0x22;        // generic data before
        rom[0x0E1A] = 0xAA; rom[0x0E1B] = 0xBB;        // range bytes
        rom[0x0E1C] = 0xCC; rom[0x0E1D] = 0xDD;
        rom[0x0E1E] = 0x33; rom[0x0E1F] = 0x44;        // generic data after
        // Make adjacent bytes reachable via a synthetic code-entry path that
        // labels $CE18 and $CE1E as data block starts.
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        // Vector points to $C000 = nothing (BRK at 0); analysis just runs.
        setField("ROM", rom);

        setupFixedVectorTable();
        File f = writeTempConfig("ranges-bounded",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);
        NESrev.runAnalysisToFixedPoint();

        String output = captureDisassemble();
        // Range start is labeled.
        assertContainsLine(output, "LCE1A:");
        // The .DB for the range starts with $AA — distinct from the preceding
        // generic data block (which ends at $CE19, before the range start).
        assertTrue("range emits as a distinct .DB starting at $AA",
            output.contains("LCE1A:") && output.indexOf("LCE1A:") < output.indexOf("$AA"));
    }

    private static String captureDisassemble() {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        System.setOut(new PrintStream(baos));
        try {
            NESrev.verifyDataLabels();
            NESrev.disassemble();
        } finally {
            System.setOut(originalOut);
        }
        return baos.toString();
    }

    private static void assembleWithXasm(File asmFile, File binFile, String context) throws Exception {
        ProcessBuilder pb = new ProcessBuilder(
            "xasm", "--pure-binary", "-o", binFile.getAbsolutePath(), asmFile.getAbsolutePath());
        pb.redirectErrorStream(true);
        Process p;
        try {
            p = pb.start();
        } catch (java.io.IOException ex) {
            throw new AssertionError("xasm is required on PATH to reassemble " + context, ex);
        }
        byte[] stdout = p.getInputStream().readAllBytes();
        int rc = p.waitFor();
        if (rc != 0) {
            throw new AssertionError("xasm failed (rc=" + rc + ") on " + context + ":\n"
                + new String(stdout));
        }
    }

    private static void assertContainsLine(String haystack, String needle) {
        testsRun++;
        if (!haystack.contains(needle)) {
            throw new AssertionError("expected output to contain '" + needle + "'; got:\n" + haystack);
        }
    }

    private static void testInlineCallsRejectsUppercaseHeader() throws Exception {
        // Spec §5.1 requires the header to match exactly. Uppercase variants
        // must be rejected so a typo doesn't silently pass.
        File f = writeTempConfig("inlinecalls-upper",
            "Callee|Layout\n$EB0A|u8\n");
        expectConfigError("uppercase header rejected",
            f.getAbsolutePath(), true, "expected header");
    }

    private static void testDataRangesRejectsUppercaseHeader() throws Exception {
        File f = writeTempConfig("dataranges-upper",
            "Start|Length\n$CD20|4\n");
        expectConfigError("uppercase header rejected",
            f.getAbsolutePath(), false, "expected header");
    }

    private static void testConflictRecordVsRecordOverlap() throws Exception {
        // Two callsites whose configured records overlap. The outer callsite
        // is reached via the reset vector; the inner one is seeded via
        // codeentries. In pass 1 neither record is blocked, both JSRs trace
        // successfully and add themselves to newlyDiscoveredCallsites. In
        // pass 2, blockKnownInlineRecords processes $C040 first (TreeMap
        // order) and blocks $C043-$C053; processing $C04F then attempts to
        // block $C052 and detects the overlap.
        resetState();
        int[] rom = makeRom();
        // Outer callsite at $C040: JSR $CFFE with bytes(16). Record is
        // $C043-$C053 (exclusive).
        rom[0x0040] = 0x20; rom[0x0041] = 0xFE; rom[0x0042] = 0xCF;
        // Inner callsite at $C04F: JSR $CFFC with bytes(2). Record is
        // $C052-$C054 (exclusive). Overlaps at $C052.
        rom[0x004F] = 0x20; rom[0x0050] = 0xFC; rom[0x0051] = 0xCF;
        // Continuation RTS.
        rom[0x0054] = 0x60;
        // Callees.
        rom[0x0FFC] = 0x60;
        rom[0x0FFE] = 0x60;
        // Reset vector -> $C040 (outer callsite).
        rom[0x3FFC] = 0x40; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        // Seed the inner callsite via codeentries so it's discovered in
        // pass 1 independently of the outer JSR's linear flow.
        java.util.ArrayList<Integer> entries = new java.util.ArrayList<Integer>();
        entries.add(0x004F);
        setField("codeEntries", entries);

        loadInlineCallsConfig(
            "callee|layout\n"
            + "$CFFC|bytes(2)\n"
            + "$CFFE|bytes(16)\n");

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for record-vs-record overlap");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("overlaps already-blocked byte")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictVectorTargetIsBlocked() throws Exception {
        // The reset vector at $FFFC points to $CE1A, which is inside a
        // configured data range. The fixed-vector application path must
        // detect this and fail.
        resetState();
        int[] rom = makeRom();
        rom[0x3FFC] = 0x1A; rom[0x3FFD] = 0xCE;       // reset vector -> $CE1A (blocked)
        setField("ROM", rom);

        setupFixedVectorTable();
        File f = writeTempConfig("conflict-vector",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for vector into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("inline-data conflict")
                || !ex.getMessage().contains("fixed vector")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
            if (!ex.getMessage().contains("dataranges config line 2")) {
                throw new AssertionError("missing data range source line: " + ex.getMessage());
            }
        }
    }

    private static void testConflictCodeEntryTargetIsBlocked() throws Exception {
        resetState();
        int[] rom = makeRom();
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        rom[0x0000] = 0x60;
        setField("ROM", rom);

        setupFixedVectorTable();
        // Codeentries entry [0] -> $CE1A is inside the blocked range.
        java.util.ArrayList<Integer> entries = new java.util.ArrayList<Integer>();
        entries.add(0x0E1A);
        setField("codeEntries", entries);

        File f = writeTempConfig("conflict-codeentry",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for codeentry into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("codeentries entry")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictCodePointerTargetIsBlocked() throws Exception {
        resetState();
        int[] rom = makeRom();
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        rom[0x0000] = 0x60;
        // Code-pointer table at $C100 with one entry targeting $CE1A (blocked).
        rom[0x0100] = 0x1A; rom[0x0101] = 0xCE;
        setField("ROM", rom);

        // User-supplied code-pointer table (not the fixed-vector table).
        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x0100);
        counts.add(1);
        // Then append fixed-vector table.
        starts.add(0x3FFA);
        counts.add(3);
        setField("codePointersStart", starts);
        setField("codePointersCount", counts);
        setField("dataPointersStart", new java.util.ArrayList<Integer>());
        setField("dataPointersCount", new java.util.ArrayList<Integer>());
        setField("codeEntries", new java.util.ArrayList<Integer>());
        setField("userCodePointersCount", 1);

        File f = writeTempConfig("conflict-codeptr",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for code-pointer into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("code-pointer table")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testCodePointerTableSkipsNonRomTarget() throws Exception {
        resetState();
        int[] rom = makeRom();
        // Table bytes are still pointer-table data, but $0010 is not a ROM
        // pointer target and must not seed arbitrary PRG offset $0010 as code.
        rom[0x0100] = 0x10; rom[0x0101] = 0x00;
        rom[0x0010] = 0x60;
        setField("ROM", rom);

        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x0100);
        counts.add(1);
        setField("codePointersStart", starts);
        setField("codePointersCount", counts);
        setField("userCodePointersCount", 1);

        NESrev.runAnalysisPass();

        assertTrue("non-ROM code-pointer table byte 0 marked as pointer", NESrev.isPtr(0x0100));
        assertTrue("non-ROM code-pointer table byte 1 marked as pointer", NESrev.isPtr(0x0101));
        assertFalse("non-ROM code-pointer target should not be traced", NESrev.isCode(0x0010));
        assertFalse("non-ROM code-pointer target should not be labeled", NESrev.isLabel(0x0010));
    }

    private static void testCodePointerTableTracesMirrorWindowTarget() throws Exception {
        resetState();
        int[] rom = makeRom();
        // $8000 is a valid NROM-128 mirror-window code pointer to PRG offset 0.
        rom[0x0100] = 0x00; rom[0x0101] = 0x80;
        rom[0x0000] = 0x60;
        setField("ROM", rom);

        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x0100);
        counts.add(1);
        setField("codePointersStart", starts);
        setField("codePointersCount", counts);
        setField("userCodePointersCount", 1);

        NESrev.runAnalysisPass();

        assertTrue("mirror-window code-pointer target should be traced", NESrev.isCode(0x0000));
        assertTrue("mirror-window code-pointer target should be labeled", NESrev.isLabel(0x0000));
    }

    private static void testDataPointerTableSkipsNonRomTarget() throws Exception {
        resetState();
        int[] rom = makeRom();
        // $0010 is not a ROM data pointer target and must not create a stray
        // PRG label at masked offset $0010.
        rom[0x0100] = 0x10; rom[0x0101] = 0x00;
        setField("ROM", rom);

        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x0100);
        counts.add(1);
        setField("dataPointersStart", starts);
        setField("dataPointersCount", counts);

        NESrev.runAnalysisPass();

        assertTrue("non-ROM data-pointer table byte 0 marked as pointer", NESrev.isPtr(0x0100));
        assertTrue("non-ROM data-pointer table byte 1 marked as pointer", NESrev.isPtr(0x0101));
        assertFalse("non-ROM data-pointer target should not be labeled", NESrev.isLabel(0x0010));
    }

    private static void testConflictCodePointerTableByteIsBlocked() throws Exception {
        resetState();
        int[] rom = makeRom();
        // Code-pointer table bytes at $C100 are explicitly configured as data.
        rom[0x0100] = 0x00; rom[0x0101] = 0xC0;
        setField("ROM", rom);

        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x0100);
        counts.add(1);
        setField("codePointersStart", starts);
        setField("codePointersCount", counts);
        setField("userCodePointersCount", 1);

        File f = writeTempConfig("conflict-codeptr-table-byte",
            "start|length\n$C100|2\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisPass();
            testsRun++;
            throw new AssertionError("expected ConfigException for code-pointer table byte in blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("code-pointer table")
                || !ex.getMessage().contains("blocked by data range")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictDataPointerTableByteIsBlocked() throws Exception {
        resetState();
        int[] rom = makeRom();
        // Data-pointer table bytes at $C100 are explicitly configured as data.
        rom[0x0100] = 0x00; rom[0x0101] = 0xC0;
        setField("ROM", rom);

        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x0100);
        counts.add(1);
        setField("dataPointersStart", starts);
        setField("dataPointersCount", counts);

        File f = writeTempConfig("conflict-dataptr-table-byte",
            "start|length\n$C100|2\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisPass();
            testsRun++;
            throw new AssertionError("expected ConfigException for data-pointer table byte in blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("data-pointer table")
                || !ex.getMessage().contains("blocked by data range")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictDataRangeContinuationTargetIsBlockedInlineRecord() throws Exception {
        resetState();
        int[] rom = makeRom();
        // Known inline record at $C103-$C104. A data range ending at $C103
        // tries to seed its continuation into the blocked record byte.
        rom[0x0100] = 0x20; rom[0x0101] = 0xFE; rom[0x0102] = 0xCF; // JSR $CFFE
        rom[0x0103] = 0xAA; rom[0x0104] = 0xBB;
        rom[0x0105] = 0x60;
        rom[0x0FFE] = 0x60;
        setField("ROM", rom);

        loadInlineCallsConfig("callee|layout\n$CFFE|bytes(2)\n");
        NESrev.InlineCallsConfig cfg = (NESrev.InlineCallsConfig) getField("inlineCalls");
        NESrev.InlineCallEntry entry = cfg.findByCallee(0x0FFE);
        TreeMap<Integer, NESrev.ResolvedRecord> known = new TreeMap<Integer, NESrev.ResolvedRecord>();
        known.put(0x0100, NESrev.resolveRecord(0x0100, entry));
        setField("knownCallsites", known);

        File f = writeTempConfig("conflict-range-continuation",
            "start|length\n$C101|2\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisPass();
            testsRun++;
            throw new AssertionError("expected ConfigException for data range continuation into blocked record");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("data range continuation")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
            if (!ex.getMessage().contains("blocked by inline record")) {
                throw new AssertionError("missing blocking source: " + ex.getMessage());
            }
            if (!ex.getMessage().contains("inlinecalls config line 2")) {
                throw new AssertionError("missing inlinecalls source line: " + ex.getMessage());
            }
        }
    }

    private static void testConflictJmpTargetIsBlocked() throws Exception {
        resetState();
        int[] rom = makeRom();
        rom[0x0000] = 0x4C; rom[0x0001] = 0x1A; rom[0x0002] = 0xCE; // JMP $CE1A
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        File f = writeTempConfig("conflict-jmp",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for JMP into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("JMP at $C000")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictBranchTargetIsBlocked() throws Exception {
        resetState();
        int[] rom = makeRom();
        // $CE17: BNE +1 -> target $CE1A. $CE1A is inside the blocked range.
        rom[0x0E17] = 0xD0; rom[0x0E18] = 0x01;
        rom[0x0E19] = 0x60;
        rom[0x3FFC] = 0x17; rom[0x3FFD] = 0xCE;     // reset vector -> $CE17
        setField("ROM", rom);

        setupFixedVectorTable();
        File f = writeTempConfig("conflict-branch",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for branch into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("relative branch at $CE17")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictInlinePtrCodeTargetIsBlocked() throws Exception {
        resetState();
        // $C000: JSR $CFFE ; ptr16(code) encoded $CE1A (blocked) ; RTS
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF;
        rom[0x0003] = 0x1A; rom[0x0004] = 0xCE;       // encoded $CE1A
        rom[0x0005] = 0x60;
        rom[0x0FFE] = 0x60;
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|ptr16(code)\n");
        File f = writeTempConfig("conflict-inlineptr",
            "start|length\n$CE1A|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for inline ptr16(code) into blocked range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("inline ptr16(code)")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testConflictInstructionOperandStraddlesRange() throws Exception {
        // The instruction at $C000 is `LDA $CE1A,X` (3 bytes). Its operand
        // bytes overlap a configured data range starting at $C001. The
        // operand-blocked check in processCodeSingle must fail.
        resetState();
        int[] rom = makeRom();
        rom[0x0000] = 0xBD; rom[0x0001] = 0x1A; rom[0x0002] = 0xCE; // LDA $CE1A,X
        rom[0x0003] = 0x60;
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        // Range starts at $C001 (PRG 0x0001) — straddles the LDA operand.
        File f = writeTempConfig("conflict-operand",
            "start|length\n$C001|2\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for operand straddling range");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("operand of instruction at $C000")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testCountedPayloadOverrunFails() throws Exception {
        // counted8 at the very end of ROM: count byte at $FFFE, claims 5
        // payload bytes. Only 1 byte (at $FFFF) is available.
        resetState();
        int[] rom = makeRom();
        rom[0x3FFB] = 0x20; rom[0x3FFC] = 0xFC; rom[0x3FFD] = 0xCF; // JSR $CFFC at $FFFB
        rom[0x3FFE] = 0x05;                                          // count byte
        rom[0x3FFF] = 0x00;
        rom[0x0FFC] = 0x60;
        setField("ROM", rom);

        loadInlineCallsConfig("callee|layout\n$CFFC|counted8\n");
        NESrev.InlineCallsConfig cfg = (NESrev.InlineCallsConfig) getField("inlineCalls");
        NESrev.InlineCallEntry entry = cfg.findByCallee(0x0FFC);

        try {
            NESrev.resolveRecord(0x3FFB, entry);
            testsRun++;
            throw new AssertionError("expected ConfigException for counted8 payload overrun");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("counted8 payload of 5 bytes exceeds ROM")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testRestartLoopNonConvergenceThrowsConfigException() throws Exception {
        resetState();
        int[] rom = makeRom();
        rom[0x0000] = 0x20; rom[0x0001] = 0xFE; rom[0x0002] = 0xCF; // JSR $CFFE
        rom[0x0003] = 0xAA;
        rom[0x0004] = 0x60;
        rom[0x0FFE] = 0x60;
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig("callee|layout\n$CFFE|bytes(1)\n");
        setField("analysisPassLimit", 0);

        try {
            NESrev.runAnalysisToFixedPoint();
            testsRun++;
            throw new AssertionError("expected ConfigException for non-convergence safety cap");
        } catch (NESrev.ConfigException ex) {
            testsRun++;
            if (!ex.getMessage().contains("did not converge")) {
                throw new AssertionError("wrong message: " + ex.getMessage());
            }
        }
    }

    private static void testNoOptionOutputIsUnchanged() throws Exception {
        // Spec §12.1 item 13 / §9.3: without -inlinecalls and -dataranges,
        // output must remain unchanged from pre-feature NESrev. The strongest
        // demonstration is end-to-end: with empty configs, the disassembled
        // output must reassemble byte-identically to the source ROM, and the
        // map/state must contain no feature artifacts.
        resetState();
        int[] rom = makeRom();
        // Reset vector → $C000. Routine: JSR $C100 ; RTS.
        rom[0x0000] = 0x20; rom[0x0001] = 0x00; rom[0x0002] = 0xC1;
        rom[0x0003] = 0x60;
        // $C100: chain of typical instructions covering several addressing
        // modes so the no-option path exercises representative code.
        rom[0x0100] = 0xA9; rom[0x0101] = 0x42;                    // LDA #$42
        rom[0x0102] = 0x8D; rom[0x0103] = 0x00; rom[0x0104] = 0x20; // STA $2000
        rom[0x0105] = 0xD0; rom[0x0106] = 0xFE;                    // BNE $-0 (self loop displaced; xasm round-trips as $-0)
        // Use a forward branch instead to avoid relative-encoding ambiguity:
        rom[0x0105] = 0xD0; rom[0x0106] = 0x01;                    // BNE +1 -> $C108
        rom[0x0107] = 0x60;                                        // RTS (skipped)
        rom[0x0108] = 0x60;                                        // RTS (branch target)
        // Some data after the routine so .DB emission also gets exercised
        // (rom is otherwise zeros; this puts a sequence after the labeled code).
        rom[0x0200] = 0xDE; rom[0x0201] = 0xAD; rom[0x0202] = 0xBE; rom[0x0203] = 0xEF;
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);
        setupFixedVectorTable();

        // No -inlinecalls / -dataranges supplied — fields stay at EMPTY (reset
        // in resetState). Configs are explicitly empty here for the test to be
        // self-evidently the "no-option" path.
        setField("inlineCalls", NESrev.InlineCallsConfig.EMPTY);
        setField("dataRanges", NESrev.DataRangesConfig.EMPTY);

        NESrev.runAnalysisToFixedPoint();

        // No feature artifacts in state.
        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        for (int i = 0; i < blocked.length; i++) {
            if (blocked[i]) {
                throw new AssertionError("no-option run produced blocked byte at $"
                    + Integer.toHexString(0xC000 + i));
            }
        }
        testsRun++;
        TreeMap<?, ?> known = (TreeMap<?, ?>) getField("knownCallsites");
        assertEquals("no inline records discovered with empty config", 0, known.size());

        // The output must reassemble byte-identically to the source ROM.
        String asm = captureDisassemble();
        File asmFile = File.createTempFile("nesrev-nooption-", ".asm");
        asmFile.deleteOnExit();
        try (FileWriter w = new FileWriter(asmFile)) {
            w.write(asm);
        }
        File binFile = File.createTempFile("nesrev-nooption-", ".o");
        binFile.deleteOnExit();
        assembleWithXasm(asmFile, binFile, "no-option output");
        byte[] produced = Files.readAllBytes(binFile.toPath());
        testsRun++;
        if (produced.length != 0x4000) {
            throw new AssertionError("xasm produced " + produced.length
                + " bytes; expected 16384");
        }
        for (int i = 0; i < 0x4000; i++) {
            int expected = rom[i] & 0xFF;
            int actual = produced[i] & 0xFF;
            if (expected != actual) {
                throw new AssertionError("no-option reassembly mismatch at PRG offset 0x"
                    + Integer.toHexString(i) + ": expected $"
                    + Integer.toHexString(expected) + ", got $"
                    + Integer.toHexString(actual));
            }
        }
        testsRun++;
    }

    private static void testNoOptionUnlabeledBackwardBranchOutputMatchesMaster() throws Exception {
        // Characterization for master output: this branch must not change
        // default no-option formatting for unlabeled backward branches.
        resetState();
        int[] rom = makeRom();
        int[] map = new int[0x4000];
        int data = getIntField("DATA");
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        int code = getIntField("CODE");
        int instr = getIntField("INSTR");
        rom[0x0100] = 0xD0; rom[0x0101] = 0xFC; // BNE backward, target unlabeled
        map[0x0100] = code | instr;
        map[0x0101] = code;
        setField("ROM", rom);
        setField("map", map);

        String asm = captureDisassemble();
        assertContainsLine(asm, "BNE $-0");
    }

    private static void testSyntheticIntegrationReassembles() throws Exception {
        // 16 KB synthetic fixture per spec §12.2. Covers all behaviors that
        // can shift binary output:
        //   - reset vector → routine with chained inline calls
        //   - bytes(N) payload whose bytes decode as valid opcodes
        //   - ptr16(code,+1) field whose encoded word and adjusted target
        //     differ, exercising the `.DW Label-1` expression
        //   - ptr16(data) target whose first byte is a valid opcode
        //   - data range followed by executable code at its exclusive end
        // After analysis we capture the disassembled output, write it to a
        // temp .asm file, invoke xasm, and assert the produced PRG is
        // byte-identical to the synthetic ROM.
        resetState();
        int[] rom = makeRom();

        // $C000 entry routine:
        //   $C000-$C002: JSR $CFF0   (outer call; bytes(2) record at $C003)
        //   $C003-$C004: $0D $0E      (bytes(2) — opcode-like payload)
        //   $C005-$C007: JSR $CFE0   (data-ptr call; ptr16(data) record at $C008)
        //   $C008-$C009: $00 $C3     (encoded $C300 — data ptr target)
        //   $C00A-$C00C: JSR $CFD0   (code-ptr+1 call; ptr16(code,+1) at $C00D)
        //   $C00D-$C00E: $FF $C1     (encoded $C1FF — adjusted target $C200)
        //   $C00F:       RTS
        rom[0x0000] = 0x20; rom[0x0001] = 0xF0; rom[0x0002] = 0xCF;
        rom[0x0003] = 0x0D; rom[0x0004] = 0x0E;
        rom[0x0005] = 0x20; rom[0x0006] = 0xE0; rom[0x0007] = 0xCF;
        rom[0x0008] = 0x00; rom[0x0009] = 0xC3;
        rom[0x000A] = 0x20; rom[0x000B] = 0xD0; rom[0x000C] = 0xCF;
        rom[0x000D] = 0xFF; rom[0x000E] = 0xC1;
        rom[0x000F] = 0x60;

        // Adjusted code-pointer target.
        rom[0x0200] = 0x60;
        // Data-pointer target whose first byte looks like LDA abs.
        rom[0x0300] = 0xAD; rom[0x0301] = 0x00; rom[0x0302] = 0x00;

        // Callees.
        rom[0x0FD0] = 0x60;
        rom[0x0FE0] = 0x60;
        rom[0x0FF0] = 0x60;

        // Data range $C400+4 with opcode-like payload, followed by code.
        rom[0x0400] = 0xA9; rom[0x0401] = 0xB9;
        rom[0x0402] = 0xC9; rom[0x0403] = 0xD9;
        rom[0x0404] = 0x60;

        // Reset vector → $C000.
        rom[0x3FFC] = 0x00; rom[0x3FFD] = 0xC0;
        setField("ROM", rom);

        setupFixedVectorTable();
        loadInlineCallsConfig(
            "callee|layout\n"
            + "$CFD0|ptr16(code,+1)\n"
            + "$CFE0|ptr16(data)\n"
            + "$CFF0|bytes(2)\n");
        File f = writeTempConfig("synthetic-ranges",
            "start|length\n$C400|4\n");
        NESrev.DataRangesConfig dr = NESrev.DataRangesConfig.parse(f.getAbsolutePath());
        setField("dataRanges", dr);

        NESrev.runAnalysisToFixedPoint();

        // Sanity-check the analysis state before reassembling.
        assertFalse("outer record byte $C003 not code", NESrev.isCode(0x0003));
        assertFalse("data-ptr record byte $C008 not code", NESrev.isCode(0x0008));
        assertFalse("code-ptr record byte $C00D not code", NESrev.isCode(0x000D));
        assertTrue("final RTS at $C00F is code", NESrev.isCode(0x000F));
        assertTrue("adjusted code target $C200 traced", NESrev.isCode(0x0200));
        assertTrue("data target $C300 labeled", NESrev.isLabel(0x0300));
        assertFalse("data target $C300 not code", NESrev.isCode(0x0300));
        boolean[] blocked = (boolean[]) getField("blockedFromCode");
        for (int i = 0x0400; i < 0x0404; i++) {
            assertTrue("range byte $" + Integer.toHexString(0xC000 + i) + " blocked", blocked[i]);
        }
        assertTrue("range continuation $C404 is code", NESrev.isCode(0x0404));

        // Capture the asm. Spec §9.1 mandates `.DW LC200-1` for the
        // ptr16(code,+1) field (encoded $C1FF + 1 = $C200).
        String asm = captureDisassemble();
        assertContainsLine(asm, ".DB $0D,$0E");
        assertContainsLine(asm, ".DW LC300");
        assertContainsLine(asm, ".DW LC200-1");

        // Reassemble the generated asm and assert byte-identical output.
        File asmFile = File.createTempFile("nesrev-synth-", ".asm");
        asmFile.deleteOnExit();
        try (FileWriter w = new FileWriter(asmFile)) {
            w.write(asm);
        }
        File binFile = File.createTempFile("nesrev-synth-", ".o");
        binFile.deleteOnExit();
        assembleWithXasm(asmFile, binFile, "synthetic integration output");
        byte[] produced = Files.readAllBytes(binFile.toPath());
        testsRun++;
        if (produced.length != 0x4000) {
            throw new AssertionError("xasm produced " + produced.length
                + " bytes; expected 16384");
        }
        for (int i = 0; i < 0x4000; i++) {
            int expected = rom[i] & 0xFF;
            int actual = produced[i] & 0xFF;
            if (expected != actual) {
                throw new AssertionError("reassembly mismatch at PRG offset 0x"
                    + Integer.toHexString(i) + ": expected $"
                    + Integer.toHexString(expected) + ", got $"
                    + Integer.toHexString(actual));
            }
        }
        testsRun++;
    }

    private static int[] makeRom() {
        return new int[0x4000];
    }

    private static void setupFixedVectorTable() throws Exception {
        java.util.ArrayList<Integer> starts = new java.util.ArrayList<Integer>();
        java.util.ArrayList<Integer> counts = new java.util.ArrayList<Integer>();
        starts.add(0x3FFA);
        counts.add(3);
        setField("codePointersStart", starts);
        setField("codePointersCount", counts);
        setField("dataPointersStart", new java.util.ArrayList<Integer>());
        setField("dataPointersCount", new java.util.ArrayList<Integer>());
        setField("codeEntries", new java.util.ArrayList<Integer>());
        setField("userCodePointersCount", 0);
    }

    private static void loadInlineCallsConfig(String content) throws Exception {
        File f = writeTempConfig("inlinecalls-load", content);
        NESrev.InlineCallsConfig cfg = NESrev.InlineCallsConfig.parse(f.getAbsolutePath());
        setField("inlineCalls", cfg);
    }

    private static void resetState() throws Exception {
        setField("toHtml", false);
        setField("ROM", new int[0x4000]);
        int data = getIntField("DATA");
        int[] map = new int[0x4000];
        for (int i = 0; i < map.length; i++) {
            map[i] = data;
        }
        setField("map", map);
        setField("codeWorklist", new ArrayDeque<Integer>());
        setField("processCodeActive", false);
        setField("blockedFromCode", new boolean[0x4000]);
        setField("inlineCalls", NESrev.InlineCallsConfig.EMPTY);
        setField("dataRanges", NESrev.DataRangesConfig.EMPTY);
        setField("knownCallsites", new TreeMap<Integer, NESrev.ResolvedRecord>());
        setField("newlyDiscoveredCallsites", new java.util.LinkedHashSet<Integer>());
        setField("analysisPassLimit", 0x4000);
        setField("codePointersStart", new java.util.ArrayList<Integer>());
        setField("codePointersCount", new java.util.ArrayList<Integer>());
        setField("dataPointersStart", new java.util.ArrayList<Integer>());
        setField("dataPointersCount", new java.util.ArrayList<Integer>());
        setField("codeEntries", new java.util.ArrayList<Integer>());
        setField("userCodePointersCount", 0);
    }

    private static void setField(String name, Object value) throws Exception {
        Field f = NESrev.class.getDeclaredField(name);
        f.setAccessible(true);
        f.set(null, value);
    }

    private static Object getField(String name) throws Exception {
        Field f = NESrev.class.getDeclaredField(name);
        f.setAccessible(true);
        return f.get(null);
    }

    private static int getIntField(String name) throws Exception {
        Field f = NESrev.class.getDeclaredField(name);
        f.setAccessible(true);
        return f.getInt(null);
    }

    private static void assertTrue(String msg, boolean condition) {
        testsRun++;
        if (!condition) {
            throw new AssertionError(msg);
        }
    }

    private static void assertEquals(String msg, int expected, int actual) {
        testsRun++;
        if (expected != actual) {
            throw new AssertionError(msg + " (expected " + expected + ", got " + actual + ")");
        }
    }

    private static void assertEquals(String msg, String expected, String actual) {
        testsRun++;
        if (!expected.equals(actual)) {
            throw new AssertionError(msg + " (expected \"" + expected + "\", got \"" + actual + "\")");
        }
    }

    private static String hex(int op) {
        String s = Integer.toHexString(op & 0xFF).toUpperCase();
        return "0x" + (s.length() == 1 ? "0" + s : s);
    }
}
