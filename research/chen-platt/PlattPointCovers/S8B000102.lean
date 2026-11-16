import PlattPointSubsetKernel
import PlattPointPackets.S7B000243
import PlattPointPackets.S7B000244
import PlattPointPackets.S7B000245
import PlattPointPackets.S7B000246
import PlattPointPackets.S7B000247
import PlattPointPackets.S7B000248
import PlattPointPackets.S7B000249
import PlattPointPackets.S7B000250
import PlattPointPackets.S7B000251
import PlattPointPackets.S7B000252
import PlattPointPackets.S7B000253
import PlattPointPackets.S7B000254
import PlattPointPackets.S7B000255
import PlattPointPackets.S7B000256
import PlattPointPackets.S7B000257
import PlattPointPackets.S7B000258
import PlattPointPackets.S7B000259
import PlattPointPackets.S7B000260
import PlattGlobalGrid.S8B000102
namespace ChenEffective.PlattWindow.PointCovers.S8B000102
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000243.points ++ ChenEffective.PlattWindow.PointPackets.S7B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000247.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000249.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000250.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000251.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000252.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000253.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000254.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000255.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000256.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000257.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000258.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000259.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000260.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000102.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000102.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000102
