import PlattPointSubsetKernel
import PlattPointPackets.S1B000369
import PlattPointPackets.S1B000370
import PlattPointPackets.S1B000371
import PlattPointPackets.S1B000372
import PlattGlobalGrid.S6B000026
namespace ChenEffective.PlattWindow.PointCovers.S6B000026
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000369.points ++ ChenEffective.PlattWindow.PointPackets.S1B000370.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000371.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000372.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000026.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000026.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000026
