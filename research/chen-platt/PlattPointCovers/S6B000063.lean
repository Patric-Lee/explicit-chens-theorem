import PlattPointSubsetKernel
import PlattPointPackets.S1B000490
import PlattPointPackets.S1B000491
import PlattPointPackets.S1B000492
import PlattPointPackets.S1B000493
import PlattPointPackets.S1B000494
import PlattGlobalGrid.S6B000063
namespace ChenEffective.PlattWindow.PointCovers.S6B000063
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000490.points ++ ChenEffective.PlattWindow.PointPackets.S1B000491.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000492.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000493.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000494.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000063.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000063.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000063
