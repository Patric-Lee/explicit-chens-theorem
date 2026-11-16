import PlattPointSubsetKernel
import PlattPointPackets.S5B000167
import PlattPointPackets.S5B000168
import PlattPointPackets.S5B000169
import PlattPointPackets.S5B000170
import PlattPointPackets.S5B000171
import PlattPointPackets.S5B000172
import PlattPointPackets.S5B000173
import PlattPointPackets.S5B000174
import PlattPointPackets.S5B000175
import PlattPointPackets.S5B000176
import PlattPointPackets.S5B000177
import PlattPointPackets.S5B000178
import PlattGlobalGrid.S8B000052
namespace ChenEffective.PlattWindow.PointCovers.S8B000052
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000167.points ++ ChenEffective.PlattWindow.PointPackets.S5B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000176.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000178.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000052.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000052.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000052
