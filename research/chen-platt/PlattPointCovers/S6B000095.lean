import PlattPointSubsetKernel
import PlattPointPackets.S1B000628
import PlattPointPackets.S1B000629
import PlattPointPackets.S1B000630
import PlattPointPackets.S1B000631
import PlattPointPackets.S1B000632
import PlattPointPackets.S1B000633
import PlattGlobalGrid.S6B000095
namespace ChenEffective.PlattWindow.PointCovers.S6B000095
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000628.points ++ ChenEffective.PlattWindow.PointPackets.S1B000629.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000630.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000631.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000632.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000633.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000095.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000095.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000095
