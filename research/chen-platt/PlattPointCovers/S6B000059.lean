import PlattPointSubsetKernel
import PlattPointPackets.S1B000475
import PlattPointPackets.S1B000476
import PlattPointPackets.S1B000477
import PlattPointPackets.S1B000478
import PlattPointPackets.S1B000479
import PlattGlobalGrid.S6B000059
namespace ChenEffective.PlattWindow.PointCovers.S6B000059
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000475.points ++ ChenEffective.PlattWindow.PointPackets.S1B000476.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000477.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000478.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000479.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000059.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000059.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000059
