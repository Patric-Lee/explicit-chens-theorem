import PlattPointSubsetKernel
import PlattPointPackets.S1B000046
import PlattPointPackets.S1B000047
import PlattGlobalGrid.S3B000056
namespace ChenEffective.PlattWindow.PointCovers.S3B000056
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000046.points ++ ChenEffective.PlattWindow.PointPackets.S1B000047.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000056.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000056.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000056
