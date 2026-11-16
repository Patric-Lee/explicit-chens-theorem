import PlattPointSubsetKernel
import PlattPointPackets.S3B000038
import PlattPointPackets.S3B000039
import PlattPointPackets.S3B000040
import PlattPointPackets.S3B000041
import PlattPointPackets.S3B000042
import PlattPointPackets.S3B000043
import PlattPointPackets.S3B000044
import PlattGlobalGrid.S7B000075
namespace ChenEffective.PlattWindow.PointCovers.S7B000075
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000038.points ++ ChenEffective.PlattWindow.PointPackets.S3B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000044.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000075.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000075.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000075
