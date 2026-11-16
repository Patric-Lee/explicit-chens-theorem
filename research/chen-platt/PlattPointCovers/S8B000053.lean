import PlattPointSubsetKernel
import PlattPointPackets.S5B000178
import PlattPointPackets.S5B000179
import PlattPointPackets.S5B000180
import PlattPointPackets.S5B000181
import PlattPointPackets.S5B000182
import PlattPointPackets.S5B000183
import PlattPointPackets.S5B000184
import PlattPointPackets.S5B000185
import PlattPointPackets.S5B000186
import PlattPointPackets.S5B000187
import PlattPointPackets.S5B000188
import PlattPointPackets.S5B000189
import PlattPointPackets.S5B000190
import PlattGlobalGrid.S8B000053
namespace ChenEffective.PlattWindow.PointCovers.S8B000053
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000178.points ++ ChenEffective.PlattWindow.PointPackets.S5B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000180.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000184.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000186.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000188.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000190.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000053.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000053.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000053
