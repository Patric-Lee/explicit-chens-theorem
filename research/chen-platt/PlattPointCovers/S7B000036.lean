import PlattPointSubsetKernel
import PlattPointPackets.S2B000172
import PlattPointPackets.S2B000173
import PlattPointPackets.S2B000174
import PlattPointPackets.S2B000175
import PlattPointPackets.S2B000176
import PlattGlobalGrid.S7B000036
namespace ChenEffective.PlattWindow.PointCovers.S7B000036
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000172.points ++ ChenEffective.PlattWindow.PointPackets.S2B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000176.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000036.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000036.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000036
