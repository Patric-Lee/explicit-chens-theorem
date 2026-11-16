import PlattPointSubsetKernel
import PlattPointPackets.S1B000319
import PlattPointPackets.S1B000320
import PlattPointPackets.S1B000321
import PlattPointPackets.S1B000322
import PlattGlobalGrid.S6B000007
namespace ChenEffective.PlattWindow.PointCovers.S6B000007
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000319.points ++ ChenEffective.PlattWindow.PointPackets.S1B000320.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000321.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000322.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000007.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000007.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000007
