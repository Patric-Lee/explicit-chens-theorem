import PlattPointSubsetKernel
import PlattPointPackets.S1B000043
import PlattPointPackets.S1B000044
import PlattGlobalGrid.S3B000041
namespace ChenEffective.PlattWindow.PointCovers.S3B000041
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000043.points ++ ChenEffective.PlattWindow.PointPackets.S1B000044.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000041.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000041.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000041
