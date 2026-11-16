import PlattPointSubsetKernel
import PlattPointPackets.S3B000283
import PlattPointPackets.S3B000284
import PlattPointPackets.S3B000285
import PlattPointPackets.S3B000286
import PlattPointPackets.S3B000287
import PlattPointPackets.S3B000288
import PlattPointPackets.S3B000289
import PlattPointPackets.S3B000290
import PlattPointPackets.S3B000291
import PlattGlobalGrid.S7B000114
namespace ChenEffective.PlattWindow.PointCovers.S7B000114
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S3B000283.points ++ ChenEffective.PlattWindow.PointPackets.S3B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000285.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000286.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000287.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000288.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000289.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000290.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000291.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000114.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000114.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000114
