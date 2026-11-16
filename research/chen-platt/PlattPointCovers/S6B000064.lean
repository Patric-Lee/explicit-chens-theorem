import PlattPointSubsetKernel
import PlattPointPackets.S1B000494
import PlattPointPackets.S1B000495
import PlattPointPackets.S1B000496
import PlattPointPackets.S1B000497
import PlattPointPackets.S1B000498
import PlattGlobalGrid.S6B000064
namespace ChenEffective.PlattWindow.PointCovers.S6B000064
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000494.points ++ ChenEffective.PlattWindow.PointPackets.S1B000495.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000496.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000497.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000498.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000064.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000064.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000064
