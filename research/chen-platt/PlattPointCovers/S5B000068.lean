import PlattPointSubsetKernel
import PlattPointPackets.S1B000210
import PlattPointPackets.S1B000211
import PlattPointPackets.S1B000212
import PlattGlobalGrid.S5B000068
namespace ChenEffective.PlattWindow.PointCovers.S5B000068
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000210.points ++ ChenEffective.PlattWindow.PointPackets.S1B000211.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000212.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000068.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000068.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000068
