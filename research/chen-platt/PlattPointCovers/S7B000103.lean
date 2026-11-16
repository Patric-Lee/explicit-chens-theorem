import PlattPointSubsetKernel
import PlattPointPackets.S3B000206
import PlattPointPackets.S3B000207
import PlattPointPackets.S3B000208
import PlattPointPackets.S3B000209
import PlattPointPackets.S3B000210
import PlattPointPackets.S3B000211
import PlattPointPackets.S3B000212
import PlattPointPackets.S3B000213
import PlattGlobalGrid.S7B000103
namespace ChenEffective.PlattWindow.PointCovers.S7B000103
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000206.points ++ ChenEffective.PlattWindow.PointPackets.S3B000207.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000208.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000209.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000210.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000211.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000212.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000213.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000103.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000103.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000103
