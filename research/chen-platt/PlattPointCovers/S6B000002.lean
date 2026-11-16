import PlattPointSubsetKernel
import PlattPointPackets.S1B000308
import PlattPointPackets.S1B000309
import PlattPointPackets.S1B000310
import PlattGlobalGrid.S6B000002
namespace ChenEffective.PlattWindow.PointCovers.S6B000002
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000308.points ++ ChenEffective.PlattWindow.PointPackets.S1B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000310.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000002.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000002.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000002
