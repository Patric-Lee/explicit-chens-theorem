import PlattPointSubsetKernel
import PlattPointPackets.S1B000648
import PlattPointPackets.S2B000000
import PlattPointPackets.S2B000001
import PlattPointPackets.S2B000002
import PlattGlobalGrid.S6B000099
namespace ChenEffective.PlattWindow.PointCovers.S6B000099
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000648.points ++ ChenEffective.PlattWindow.PointPackets.S2B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000002.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000099.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000099.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000099
