import PlattPointSubsetKernel
import PlattPointPackets.S7B000176
import PlattPointPackets.S7B000177
import PlattPointPackets.S7B000178
import PlattPointPackets.S7B000179
import PlattPointPackets.S7B000180
import PlattPointPackets.S7B000181
import PlattPointPackets.S7B000182
import PlattPointPackets.S7B000183
import PlattPointPackets.S7B000184
import PlattPointPackets.S7B000185
import PlattPointPackets.S7B000186
import PlattPointPackets.S7B000187
import PlattPointPackets.S7B000188
import PlattPointPackets.S7B000189
import PlattPointPackets.S7B000190
import PlattPointPackets.S7B000191
import PlattPointPackets.S7B000192
import PlattPointPackets.S7B000193
import PlattGlobalGrid.S8B000098
namespace ChenEffective.PlattWindow.PointCovers.S8B000098
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000176.points ++ ChenEffective.PlattWindow.PointPackets.S7B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000180.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000184.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000186.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000188.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000190.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000193.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000098.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000098.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000098
