import PlattPointSubsetKernel
import PlattPointPackets.S1B000238
import PlattPointPackets.S1B000239
import PlattPointPackets.S1B000240
import PlattGlobalGrid.S5B000085
namespace ChenEffective.PlattWindow.PointCovers.S5B000085
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000238.points ++ ChenEffective.PlattWindow.PointPackets.S1B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000240.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000085.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000085.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000085
