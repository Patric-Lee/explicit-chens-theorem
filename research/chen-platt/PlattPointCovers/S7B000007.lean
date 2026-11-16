import PlattPointSubsetKernel
import PlattPointPackets.S2B000070
import PlattPointPackets.S2B000071
import PlattPointPackets.S2B000072
import PlattPointPackets.S2B000073
import PlattGlobalGrid.S7B000007
namespace ChenEffective.PlattWindow.PointCovers.S7B000007
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000070.points ++ ChenEffective.PlattWindow.PointPackets.S2B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000073.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000007.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000007.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000007
