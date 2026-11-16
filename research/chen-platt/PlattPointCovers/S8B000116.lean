import PlattPointSubsetKernel
import PlattPointPackets.S8B000183
import PlattPointPackets.S8B000184
import PlattPointPackets.S8B000185
import PlattPointPackets.S8B000186
import PlattPointPackets.S8B000187
import PlattPointPackets.S8B000188
import PlattPointPackets.S8B000189
import PlattPointPackets.S8B000190
import PlattPointPackets.S8B000191
import PlattPointPackets.S8B000192
import PlattPointPackets.S8B000193
import PlattPointPackets.S8B000194
import PlattPointPackets.S8B000195
import PlattGlobalGrid.S8B000116
namespace ChenEffective.PlattWindow.PointCovers.S8B000116
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000183.points ++ ChenEffective.PlattWindow.PointPackets.S8B000184.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000186.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000188.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000190.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000193.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000195.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000116.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000116.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000116
