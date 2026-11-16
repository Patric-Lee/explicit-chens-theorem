import PlattPointSubsetKernel
import PlattPointPackets.S1B000471
import PlattPointPackets.S1B000472
import PlattPointPackets.S1B000473
import PlattPointPackets.S1B000474
import PlattPointPackets.S1B000475
import PlattGlobalGrid.S6B000058
namespace ChenEffective.PlattWindow.PointCovers.S6B000058
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000471.points ++ ChenEffective.PlattWindow.PointPackets.S1B000472.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000473.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000474.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000475.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000058.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000058.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000058
