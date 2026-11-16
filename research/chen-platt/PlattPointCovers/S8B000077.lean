import PlattPointSubsetKernel
import PlattPointPackets.S6B000170
import PlattPointPackets.S6B000171
import PlattPointPackets.S6B000172
import PlattPointPackets.S6B000173
import PlattPointPackets.S6B000174
import PlattPointPackets.S6B000175
import PlattPointPackets.S6B000176
import PlattPointPackets.S6B000177
import PlattPointPackets.S6B000178
import PlattPointPackets.S6B000179
import PlattPointPackets.S6B000180
import PlattPointPackets.S6B000181
import PlattPointPackets.S6B000182
import PlattPointPackets.S6B000183
import PlattPointPackets.S6B000184
import PlattGlobalGrid.S8B000077
namespace ChenEffective.PlattWindow.PointCovers.S8B000077
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000170.points ++ ChenEffective.PlattWindow.PointPackets.S6B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000176.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000180.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000184.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000077.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000077.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000077
