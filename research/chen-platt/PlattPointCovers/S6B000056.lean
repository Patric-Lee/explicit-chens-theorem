import PlattPointSubsetKernel
import PlattPointPackets.S1B000464
import PlattPointPackets.S1B000465
import PlattPointPackets.S1B000466
import PlattPointPackets.S1B000467
import PlattPointPackets.S1B000468
import PlattGlobalGrid.S6B000056
namespace ChenEffective.PlattWindow.PointCovers.S6B000056
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000464.points ++ ChenEffective.PlattWindow.PointPackets.S1B000465.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000466.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000467.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000468.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000056.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000056.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000056
