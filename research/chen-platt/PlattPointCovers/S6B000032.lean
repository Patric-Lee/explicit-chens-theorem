import PlattPointSubsetKernel
import PlattPointPackets.S1B000386
import PlattPointPackets.S1B000387
import PlattPointPackets.S1B000388
import PlattPointPackets.S1B000389
import PlattGlobalGrid.S6B000032
namespace ChenEffective.PlattWindow.PointCovers.S6B000032
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000386.points ++ ChenEffective.PlattWindow.PointPackets.S1B000387.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000388.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000389.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000032.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000032.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000032
