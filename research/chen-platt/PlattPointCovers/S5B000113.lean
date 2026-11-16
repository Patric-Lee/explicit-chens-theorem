import PlattPointSubsetKernel
import PlattPointPackets.S1B000294
import PlattPointPackets.S1B000295
import PlattPointPackets.S1B000296
import PlattGlobalGrid.S5B000113
namespace ChenEffective.PlattWindow.PointCovers.S5B000113
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000294.points ++ ChenEffective.PlattWindow.PointPackets.S1B000295.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000296.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000113.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000113.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000113
