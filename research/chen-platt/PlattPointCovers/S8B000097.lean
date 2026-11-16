import PlattPointSubsetKernel
import PlattPointPackets.S7B000160
import PlattPointPackets.S7B000161
import PlattPointPackets.S7B000162
import PlattPointPackets.S7B000163
import PlattPointPackets.S7B000164
import PlattPointPackets.S7B000165
import PlattPointPackets.S7B000166
import PlattPointPackets.S7B000167
import PlattPointPackets.S7B000168
import PlattPointPackets.S7B000169
import PlattPointPackets.S7B000170
import PlattPointPackets.S7B000171
import PlattPointPackets.S7B000172
import PlattPointPackets.S7B000173
import PlattPointPackets.S7B000174
import PlattPointPackets.S7B000175
import PlattPointPackets.S7B000176
import PlattGlobalGrid.S8B000097
namespace ChenEffective.PlattWindow.PointCovers.S8B000097
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000160.points ++ ChenEffective.PlattWindow.PointPackets.S7B000161.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000164.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000167.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000176.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000097.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000097.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000097
