import PlattPointSubsetKernel
import PlattPointPackets.S3B000213
import PlattPointPackets.S3B000214
import PlattPointPackets.S3B000215
import PlattPointPackets.S3B000216
import PlattPointPackets.S3B000217
import PlattPointPackets.S3B000218
import PlattPointPackets.S3B000219
import PlattPointPackets.S3B000220
import PlattGlobalGrid.S7B000104
namespace ChenEffective.PlattWindow.PointCovers.S7B000104
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000213.points ++ ChenEffective.PlattWindow.PointPackets.S3B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000220.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000104.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000104.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000104
