import PlattPointSubsetKernel
import PlattPointPackets.S4B000249
import PlattPointPackets.S4B000250
import PlattPointPackets.S4B000251
import PlattPointPackets.S4B000252
import PlattPointPackets.S4B000253
import PlattPointPackets.S4B000254
import PlattPointPackets.S4B000255
import PlattPointPackets.S4B000256
import PlattPointPackets.S4B000257
import PlattPointPackets.S4B000258
import PlattPointPackets.S4B000259
import PlattGlobalGrid.S8B000030
namespace ChenEffective.PlattWindow.PointCovers.S8B000030
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000249.points ++ ChenEffective.PlattWindow.PointPackets.S4B000250.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000251.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000252.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000253.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000254.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000255.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000256.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000257.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000258.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000259.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000030.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000030.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000030
