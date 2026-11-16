import PlattPointSubsetKernel
import PlattPointPackets.S4B000166
import PlattPointPackets.S4B000167
import PlattPointPackets.S4B000168
import PlattPointPackets.S4B000169
import PlattPointPackets.S4B000170
import PlattPointPackets.S4B000171
import PlattPointPackets.S4B000172
import PlattPointPackets.S4B000173
import PlattPointPackets.S4B000174
import PlattPointPackets.S4B000175
import PlattGlobalGrid.S8B000021
namespace ChenEffective.PlattWindow.PointCovers.S8B000021
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000166.points ++ ChenEffective.PlattWindow.PointPackets.S4B000167.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000175.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000021.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000021.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000021
