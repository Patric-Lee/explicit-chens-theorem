import PlattPointSubsetKernel
import PlattPointPackets.S8B000164
import PlattPointPackets.S8B000165
import PlattPointPackets.S8B000166
import PlattPointPackets.S8B000167
import PlattPointPackets.S8B000168
import PlattPointPackets.S8B000169
import PlattPointPackets.S8B000170
import PlattPointPackets.S8B000171
import PlattPointPackets.S8B000172
import PlattPointPackets.S8B000173
import PlattPointPackets.S8B000174
import PlattPointPackets.S8B000175
import PlattPointPackets.S8B000176
import PlattPointPackets.S8B000177
import PlattPointPackets.S8B000178
import PlattPointPackets.S8B000179
import PlattPointPackets.S8B000180
import PlattPointPackets.S8B000181
import PlattPointPackets.S8B000182
import PlattPointPackets.S8B000183
import PlattGlobalGrid.S8B000115
namespace ChenEffective.PlattWindow.PointCovers.S8B000115
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000164.points ++ ChenEffective.PlattWindow.PointPackets.S8B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000167.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000176.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000180.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000183.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000115.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000115.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000115
