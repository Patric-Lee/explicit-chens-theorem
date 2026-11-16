import PlattPointSubsetKernel
import PlattPointPackets.S6B000184
import PlattPointPackets.S6B000185
import PlattPointPackets.S6B000186
import PlattPointPackets.S6B000187
import PlattPointPackets.S6B000188
import PlattPointPackets.S6B000189
import PlattPointPackets.S6B000190
import PlattPointPackets.S6B000191
import PlattPointPackets.S6B000192
import PlattPointPackets.S6B000193
import PlattPointPackets.S6B000194
import PlattPointPackets.S6B000195
import PlattPointPackets.S6B000196
import PlattPointPackets.S6B000197
import PlattPointPackets.S6B000198
import PlattGlobalGrid.S8B000078
namespace ChenEffective.PlattWindow.PointCovers.S8B000078
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000184.points ++ ChenEffective.PlattWindow.PointPackets.S6B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000186.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000188.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000190.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000193.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000196.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000198.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000078.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000078.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000078
