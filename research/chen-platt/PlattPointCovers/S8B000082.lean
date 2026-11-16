import PlattPointSubsetKernel
import PlattPointPackets.S6B000241
import PlattPointPackets.S6B000242
import PlattPointPackets.S6B000243
import PlattPointPackets.S6B000244
import PlattPointPackets.S6B000245
import PlattPointPackets.S6B000246
import PlattPointPackets.S6B000247
import PlattPointPackets.S6B000248
import PlattPointPackets.S6B000249
import PlattPointPackets.S6B000250
import PlattPointPackets.S6B000251
import PlattPointPackets.S6B000252
import PlattPointPackets.S6B000253
import PlattPointPackets.S6B000254
import PlattPointPackets.S6B000255
import PlattPointPackets.S6B000256
import PlattGlobalGrid.S8B000082
namespace ChenEffective.PlattWindow.PointCovers.S8B000082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000241.points ++ ChenEffective.PlattWindow.PointPackets.S6B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000243.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000247.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000249.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000250.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000251.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000252.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000253.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000254.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000255.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000256.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000082.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000082.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000082
