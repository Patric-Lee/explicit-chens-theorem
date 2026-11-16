import PlattPointSubsetKernel
import PlattPointPackets.S1B000380
import PlattPointPackets.S1B000381
import PlattPointPackets.S1B000382
import PlattPointPackets.S1B000383
import PlattGlobalGrid.S6B000030
namespace ChenEffective.PlattWindow.PointCovers.S6B000030
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000380.points ++ ChenEffective.PlattWindow.PointPackets.S1B000381.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000382.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000383.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000030.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000030.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000030
