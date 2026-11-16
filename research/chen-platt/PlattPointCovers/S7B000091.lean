import PlattPointSubsetKernel
import PlattPointPackets.S3B000130
import PlattPointPackets.S3B000131
import PlattPointPackets.S3B000132
import PlattPointPackets.S3B000133
import PlattPointPackets.S3B000134
import PlattPointPackets.S3B000135
import PlattPointPackets.S3B000136
import PlattGlobalGrid.S7B000091
namespace ChenEffective.PlattWindow.PointCovers.S7B000091
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000130.points ++ ChenEffective.PlattWindow.PointPackets.S3B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000136.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000091.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000091.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000091
