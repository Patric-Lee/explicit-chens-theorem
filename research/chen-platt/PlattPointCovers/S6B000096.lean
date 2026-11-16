import PlattPointSubsetKernel
import PlattPointPackets.S1B000633
import PlattPointPackets.S1B000634
import PlattPointPackets.S1B000635
import PlattPointPackets.S1B000636
import PlattPointPackets.S1B000637
import PlattPointPackets.S1B000638
import PlattGlobalGrid.S6B000096
namespace ChenEffective.PlattWindow.PointCovers.S6B000096
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000633.points ++ ChenEffective.PlattWindow.PointPackets.S1B000634.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000635.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000636.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000637.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000638.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000096.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000096.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000096
