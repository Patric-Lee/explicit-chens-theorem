import PlattPointSubsetKernel
import PlattPointPackets.S1B000184
import PlattPointPackets.S1B000185
import PlattPointPackets.S1B000186
import PlattGlobalGrid.S5B000050
namespace ChenEffective.PlattWindow.PointCovers.S5B000050
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000184.points ++ ChenEffective.PlattWindow.PointPackets.S1B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000186.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000050.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000050.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000050
