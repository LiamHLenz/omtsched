import logo from './logo.svg';
import './App.css';
import Navbar from './Navbar';
import { Outlet, Link } from 'react-router-dom';

function App() {
  return (
    <div className="App">
      <Navbar/>
      <Outlet />
    </div>
  );
}

export default App;
