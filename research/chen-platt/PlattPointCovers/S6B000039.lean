import PlattPointSubsetKernel
import PlattPointPackets.S1B000407
import PlattPointPackets.S1B000408
import PlattPointPackets.S1B000409
import PlattPointPackets.S1B000410
import PlattPointPackets.S1B000411
import PlattGlobalGrid.S6B000039
namespace ChenEffective.PlattWindow.PointCovers.S6B000039
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000407.points ++ ChenEffective.PlattWindow.PointPackets.S1B000408.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000409.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000410.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000411.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000039.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000039.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000039
