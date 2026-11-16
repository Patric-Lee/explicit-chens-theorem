import PlattPointSubsetKernel
import PlattPointPackets.S1B000363
import PlattPointPackets.S1B000364
import PlattPointPackets.S1B000365
import PlattPointPackets.S1B000366
import PlattGlobalGrid.S6B000024
namespace ChenEffective.PlattWindow.PointCovers.S6B000024
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000363.points ++ ChenEffective.PlattWindow.PointPackets.S1B000364.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000365.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000366.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000024.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000024.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000024
