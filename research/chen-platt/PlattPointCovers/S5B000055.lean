import PlattPointSubsetKernel
import PlattPointPackets.S1B000191
import PlattPointPackets.S1B000192
import PlattPointPackets.S1B000193
import PlattGlobalGrid.S5B000055
namespace ChenEffective.PlattWindow.PointCovers.S5B000055
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000191.points ++ ChenEffective.PlattWindow.PointPackets.S1B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000193.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000055.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000055.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000055
