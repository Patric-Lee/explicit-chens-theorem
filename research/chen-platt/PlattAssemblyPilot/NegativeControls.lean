import PlattAssemblyKernel
import PlattIncrementKernel
namespace ChenEffective.PlattWindow.AssemblyPilot
-- These arithmetic controls deliberately contain no prime-count hypothesis.
example : checkPrefixCuts 16 11 0 0 3 [⟨1,0,1⟩,⟨3,0,3⟩] = true := by decide +kernel
example : checkPrefixCuts 16 11 0 0 3 [⟨1,0,2⟩] = false := by decide +kernel
example : checkPrefixCuts 16 11 0 0 3 [⟨4,0,4⟩] = false := by decide +kernel
example : checkPrefixCuts 16 11 0 0 3 [⟨2,0,2⟩,⟨1,0,1⟩] = false := by decide +kernel
example : checkCellChain 4 8 [⟨4,6,0,0,0,0⟩,⟨6,8,0,0,0,0⟩] = true := by decide +kernel
example : checkCellChain 4 8 [⟨4,6,0,0,0,0⟩,⟨7,8,0,0,0,0⟩] = false := by decide +kernel
example : checkAssemblyCell 100 20000 0 0 0 0 ⟨4,8,0,0,0,0⟩ = true := by decide +kernel
example : checkAssemblyCell 100 20000 0 0 0 0 ⟨4,8,0,1,0,0⟩ = false := by decide +kernel
example : checkAssemblyCell 100 20000 0 1 0 0 ⟨4,8,0,0,0,0⟩ = false := by decide +kernel
example : checkIncrementSummary 4 8 3 5 [⟨4,6,1,2⟩,⟨6,8,2,3⟩] = true := by decide +kernel
example : checkIncrementSummary 4 8 3 6 [⟨4,6,1,2⟩,⟨6,8,2,3⟩] = false := by decide +kernel
end ChenEffective.PlattWindow.AssemblyPilot
