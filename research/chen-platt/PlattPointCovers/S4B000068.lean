import PlattPointSubsetKernel
import PlattPointPackets.S1B000094
import PlattPointPackets.S1B000095
import PlattGlobalGrid.S4B000068
namespace ChenEffective.PlattWindow.PointCovers.S4B000068
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000094.points ++ ChenEffective.PlattWindow.PointPackets.S1B000095.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S4B000068.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S4B000068.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S4B000068
