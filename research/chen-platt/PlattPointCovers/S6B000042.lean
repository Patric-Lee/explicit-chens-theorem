import PlattPointSubsetKernel
import PlattPointPackets.S1B000417
import PlattPointPackets.S1B000418
import PlattPointPackets.S1B000419
import PlattPointPackets.S1B000420
import PlattGlobalGrid.S6B000042
namespace ChenEffective.PlattWindow.PointCovers.S6B000042
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000417.points ++ ChenEffective.PlattWindow.PointPackets.S1B000418.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000419.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000420.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000042.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000042.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000042
