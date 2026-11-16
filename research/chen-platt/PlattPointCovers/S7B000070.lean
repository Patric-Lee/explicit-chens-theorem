import PlattPointSubsetKernel
import PlattPointPackets.S3B000012
import PlattPointPackets.S3B000013
import PlattPointPackets.S3B000014
import PlattPointPackets.S3B000015
import PlattPointPackets.S3B000016
import PlattPointPackets.S3B000017
import PlattGlobalGrid.S7B000070
namespace ChenEffective.PlattWindow.PointCovers.S7B000070
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000012.points ++ ChenEffective.PlattWindow.PointPackets.S3B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000017.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000070.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000070.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000070
