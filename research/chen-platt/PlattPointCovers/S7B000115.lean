import PlattPointSubsetKernel
import PlattPointPackets.S3B000291
import PlattPointPackets.S3B000292
import PlattPointPackets.S3B000293
import PlattPointPackets.S3B000294
import PlattPointPackets.S3B000295
import PlattPointPackets.S3B000296
import PlattPointPackets.S3B000297
import PlattPointPackets.S3B000298
import PlattGlobalGrid.S7B000115
namespace ChenEffective.PlattWindow.PointCovers.S7B000115
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000291.points ++ ChenEffective.PlattWindow.PointPackets.S3B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000295.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000298.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000115.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000115.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000115
