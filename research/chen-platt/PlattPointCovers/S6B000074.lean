import PlattPointSubsetKernel
import PlattPointPackets.S1B000533
import PlattPointPackets.S1B000534
import PlattPointPackets.S1B000535
import PlattPointPackets.S1B000536
import PlattPointPackets.S1B000537
import PlattPointPackets.S1B000538
import PlattGlobalGrid.S6B000074
namespace ChenEffective.PlattWindow.PointCovers.S6B000074
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000533.points ++ ChenEffective.PlattWindow.PointPackets.S1B000534.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000535.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000536.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000537.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000538.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000074.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000074.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000074
