import PlattPointSubsetKernel
import PlattPointPackets.S1B000008
import PlattPointPackets.S1B000009
import PlattGlobalGrid.S1B000082
namespace ChenEffective.PlattWindow.PointCovers.S1B000082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000008.points ++ ChenEffective.PlattWindow.PointPackets.S1B000009.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S1B000082.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S1B000082.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S1B000082
