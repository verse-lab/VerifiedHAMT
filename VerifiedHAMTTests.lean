import VerifiedHAMTTests.Contains
import VerifiedHAMTTests.Insert
import VerifiedHAMTTests.Map
import VerifiedHAMTTests.Set
import VerifiedHAMTTests.SetWithoutValArray
import VerifiedHAMTTests.ReleaseIR
import VerifiedHAMTTests.MapIR
import VerifiedHAMTTests.SetIR
import VerifiedHAMTTests.SetWithoutValArrayIR

/-! Default test driver: compile all proof and IR checks, then run every runtime suite. -/

def main : IO Unit := do
  VerifiedHAMT.Tests.run
  VerifiedHAMT.InsertTests.run
  VerifiedHAMT.MapTests.run
  VerifiedHAMT.SetTests.run
  VerifiedHAMT.SetWithoutValArrayTests.run
