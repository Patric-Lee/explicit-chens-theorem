import PlattPointSubsetKernel
import PlattPointPackets.S1B000440
import PlattPointPackets.S1B000441
import PlattPointPackets.S1B000442
import PlattPointPackets.S1B000443
import PlattGlobalGrid.S6B000049
namespace ChenEffective.PlattWindow.PointCovers.S6B000049
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000440.points ++ ChenEffective.PlattWindow.PointPackets.S1B000441.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000442.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000443.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000049.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000049.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000049
