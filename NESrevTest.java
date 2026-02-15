import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

public class NESrevTest {
    private static int testsRun = 0;

    public static void main(String[] args) throws Exception {
        testGetAddressMasksTo14Bits();
        testVerifyDataLabelsMarksCodeToDataBoundary();
        testProcessCodeFollowsJsrTarget();
        testProcessCodeQueuesRelativeBranchTarget();
        testPrintAddressAddsWideningSuffixForZeroPageAbsoluteOps();
        testOpcodeTablesHave256Entries();
        testProcessableOpcodesMapAsInstructions();
        testAddressingModesCoveredByProcessableOpcodes();
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
