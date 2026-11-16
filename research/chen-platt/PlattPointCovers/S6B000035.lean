import PlattPointSubsetKernel
import PlattPointPackets.S1B000395
import PlattPointPackets.S1B000396
import PlattPointPackets.S1B000397
import PlattPointPackets.S1B000398
import PlattGlobalGrid.S6B000035
namespace ChenEffective.PlattWindow.PointCovers.S6B000035
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000395.points ++ ChenEffective.PlattWindow.PointPackets.S1B000396.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000397.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000398.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000035.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000035.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000035
