"""Generate kernel proof batches for the finite automaton header."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def combine(names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f"(batch_join {combine(names[:mid])} {combine(names[mid:])})"


def main():
    out = ["module", "", "public import Staircase.DualData", "", "@[expose] public section",
           "namespace Staircase.Certificate", "", "set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0", ""]
    tests = [("start", "starts", "Machine.startFlag listedRules"),
             ("letter", "letters", "Machine.letterFlag"), ("end", "ends", "Machine.endFlag")]
    for name, field, flag in tests:
        out.append(f"private def {name}Test (i : Nat) := decide (machine.{field}[i]?.getD 0 = "
                   f"flagMask ({flag} i) machine.positions)")
    for name, f, size, step in [(n, n + "Test", 37, 1) for n, _, _ in tests] + [
            ("link", "machine.linkOK", 1111, 16)]:
        names = []
        for start in range(0, size, step):
            thm = f"{name}At{start}"
            names.append(thm)
            out.append(f"private theorem {thm} : Batch {f} {start} {min(step, size-start)} := "
                       "batch_checked (by decide +kernel)")
        out += [f"private theorem {name}All : Batch {f} 0 {size} :=", "  " + combine(names), ""]
    out += ["theorem header : machine.Header listedRules := by", "  refine ⟨?_,?_,?_,?_,?_⟩"]
    for name, _, _ in tests:
        out += ["  · intro i hi", f"    simpa only [Nat.zero_add,{name}Test,decide_eq_true_eq] using {name}All i hi"]
    out += ["  · decide +kernel", "  · intro i hi", "    have len : machine.positions.length=1111 := by decide +kernel",
            "    rw [len] at hi", "    simpa only [Nat.zero_add] using linkAll i hi", "", "end Staircase.Certificate", ""]
    (ROOT / "Staircase" / "Header.lean").write_text("\n".join(out))


if __name__ == "__main__":
    main()
