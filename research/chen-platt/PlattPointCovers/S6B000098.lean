import PlattPointSubsetKernel
import PlattPointPackets.S1B000643
import PlattPointPackets.S1B000644
import PlattPointPackets.S1B000645
import PlattPointPackets.S1B000646
import PlattPointPackets.S1B000647
import PlattPointPackets.S1B000648
import PlattGlobalGrid.S6B000098
namespace ChenEffective.PlattWindow.PointCovers.S6B000098
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000643.points ++ ChenEffective.PlattWindow.PointPackets.S1B000644.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000645.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000646.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000647.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000648.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000098.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000098.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000098
