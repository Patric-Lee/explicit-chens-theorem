import PlattPointSubsetKernel
import PlattPointPackets.S1B000595
import PlattPointPackets.S1B000596
import PlattPointPackets.S1B000597
import PlattPointPackets.S1B000598
import PlattPointPackets.S1B000599
import PlattPointPackets.S1B000600
import PlattGlobalGrid.S6B000088
namespace ChenEffective.PlattWindow.PointCovers.S6B000088
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000595.points ++ ChenEffective.PlattWindow.PointPackets.S1B000596.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000597.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000598.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000599.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000600.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000088.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000088.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000088
