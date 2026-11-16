import PlattPointSubsetKernel
import PlattPointPackets.S1B000073
import PlattPointPackets.S1B000074
import PlattGlobalGrid.S4B000027
namespace ChenEffective.PlattWindow.PointCovers.S4B000027
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000073.points ++ ChenEffective.PlattWindow.PointPackets.S1B000074.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S4B000027.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S4B000027.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S4B000027
