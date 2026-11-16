import PlattPointSubsetKernel
import PlattPointPackets.S2B000247
import PlattPointPackets.S2B000248
import PlattPointPackets.S2B000249
import PlattPointPackets.S2B000250
import PlattPointPackets.S2B000251
import PlattPointPackets.S2B000252
import PlattGlobalGrid.S7B000054
namespace ChenEffective.PlattWindow.PointCovers.S7B000054
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000247.points ++ ChenEffective.PlattWindow.PointPackets.S2B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000249.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000250.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000251.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000252.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000054.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000054.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000054
