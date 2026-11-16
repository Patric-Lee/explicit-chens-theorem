import PlattPointSubsetKernel
import PlattPointPackets.S1B000423
import PlattPointPackets.S1B000424
import PlattPointPackets.S1B000425
import PlattPointPackets.S1B000426
import PlattPointPackets.S1B000427
import PlattGlobalGrid.S6B000044
namespace ChenEffective.PlattWindow.PointCovers.S6B000044
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000423.points ++ ChenEffective.PlattWindow.PointPackets.S1B000424.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000425.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000426.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000427.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000044.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000044.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000044
